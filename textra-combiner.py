import argparse
from datetime import datetime, timezone
from functools import reduce
from itertools import chain
import re
import time
import xml.etree.ElementTree as ET

SEC_TO_MS = 1000
MIN_TO_SEC = 60


def make_lookup_tuple(e):
    """
    Given an XML ElementTree element, create a lookup tuple as:
    (phone number, Unix epoch sent to minute precision, message content).
    Normalize phone number by stripping all non-digit characters.
    Normalize message body by stripping all whitespace characters.
    Used for determining message uniqueness.
    """

    # Different cases for SMS and MMS messages, since the accompanying text is in
    # different places.
    if e.tag == "sms":
        text = e.attrib.get("body").strip()
    elif e.tag == "mms":
        for parts in e.findall("parts"):
            text = "".join(part.attrib.get("text", "").strip() for part in parts)
    else:
        text = ""

    return (
        re.sub(r"[^\d]", "", e.attrib.get("address", "NO-ADDRESS")),
        int(e.attrib.get("date")) // SEC_TO_MS // MIN_TO_SEC,
        re.sub(r"[\s]", "", text),
    )


def datetime_to_epoch(raw):
    """
    Given a time in M/D/YY H:MM AM format, convert this to Unix epoch time (in ms).
    Time is assumed to be in the local timezone.
    """
    dt = datetime.strptime(raw, "%m/%d/%y %I:%M %p")
    return int(dt.timestamp()) * SEC_TO_MS


def get_name_and_number(line):
    """
    Given the initial line of a Textra export, extracts name and number.
    Name has whitespace trimmed.
    Example: 'Conversation with John Doe (+1 (123) 456-7890)'
    returns ('John Doe', '+1 (123) 456-7890')
    """
    line = line.rstrip().replace("Conversation with ", "")
    name, number = line.split("(", 1)
    name = name.strip()
    number = number[:-1]
    return name, number


def parse_textra_line(line, number, provided_name=None):
    """
    Given a line of conversation in a Textra export, parse it into an xml
    that can be inserted into an ElementTree.
    Takes required phone number of the contact.
    Takes optional name parameter. If not provided, extracts it.
    """
    time, message = line.split("] ", maxsplit=1)
    epoch = datetime_to_epoch(time[1:])  # remove starting square bracket and parse.
    name, message = message.split(
        ": ", maxsplit=1
    )  # assumes that contacts don't have a colon in their name.
    sent_message = name == "Me"  # assumes that contacts aren't named "Me"

    # Ref. https://synctech.com.au/sms-backup-restore/fields-in-xml-backup-files/.
    attribs = {
        "protocol": "0",
        "address": str(number),
        "date": str(epoch),
        "type": ("2" if sent_message else "1"),
        "subject": "null",
        "body": str(message),
        "toa": "null",
        "sc_toa": "null",
        "service_center": "null",
        "read": "1",
        "status": "-1",
        "locked": "0",
        "date_sent": str(epoch),
        "sub_id": "1",
        "contact_name": str(provided_name) if provided_name is not None else str(name),
    }
    return ET.Element("sms", attrib=attribs)


def parse_textra_file(filepath):
    """
    Given a Textra export file, parse it into a generator of xmls that can be inserted
    into an ElementTree.
    """

    name, number = None, None
    with open(filepath, "r") as f:
        current_raw_message = (
            []
        )  # save working message as array of lines; some messages are newline separated.
        for line in f:
            line = line.strip()
            if len(line) == 0:  # blank line.
                continue
            elif name is None and number is None:  # only happens initially.
                name, number = get_name_and_number(line)
            else:
                try:  # try to parse the line as if it were a new message.
                    # See if the new line is parseable as the start of a message.
                    parse_textra_line(line, number=number, provided_name=name)
                    yield parse_textra_line(
                        " ".join(current_raw_message), number=number, provided_name=name
                    )
                    current_raw_message = [line]
                except:  # if it doesn't work, assume it's a newline continuation.
                    current_raw_message.append(line)
        # Yield final line.
        yield parse_textra_line(
            " ".join(current_raw_message), number=number, provided_name=name
        )


def strip_texts(et, strip_phrases):
    """
    Strip texts if they match a list of strip phrases. Used to remove meta texts
    such as "You received a picture."
    """
    strip_phrases = set(strip_phrases)

    # Tested this on my actual phone data and it appears that the initial loop
    # iteration doesn't catch all of the texts? For my data: the first iteration
    # captured 118 texts, the second caught 2, the third caught 1, and the fourth
    # caught 0. Very strange! I couldn't figure it out so we can use this hacky
    # workaround instead. Keep trying until we get all of them.
    while True:
        num_stripped = 0
        for msg in et.getroot():
            if msg.attrib.get("body", "").strip() in strip_phrases:
                num_stripped += 1
                et.getroot().remove(msg)
        if num_stripped == 0:
            break
    return et


def strip_invalid_address(et):
    """
    Fix MMS address issue where one MMS address is "insert-address-token", which
    causes all MMS messages to show up from "Unknown sender" or "Anonymous" (depending
    on your SMS app) in a single conversation, by removing all addr elements with that
    address.
    """

    # Eliminate "insert-address-token" addresses.
    for mms in et.getroot().findall("mms"):
        for addrs in mms.findall("addrs"):
            for addr in addrs:
                if addr.attrib.get("address", None) == "insert-address-token":
                    addrs.remove(addr)
    return et


def fix_sent_from_address(et):
    """
    Fixes issue where there is no address attribute in the MMS element.
    """
    # Try filling in MMS addresses with sent-from addresses, if they exist, otherwise
    # any address will do.
    for mms in et.getroot().findall("mms"):
        if "address" not in mms.attrib:
            for addrs in mms.findall("addrs"):
                new_address = "~".join(
                    addr.attrib.get("address", "")
                    for addr in addrs
                    if addr.attrib.get("type") == "137"
                )
                if new_address is None or new_address == "":
                    new_address = "~".join(
                        addr.attrib.get("address", "") for addr in addrs
                    )
            mms.attrib["address"] = new_address
    return et


def main(
    xml_filepath=None,
    txt_filepaths=None,
    strip_phrases=None,
    flag_strip_invalid_address=False,
    flag_fix_sent_from_address=False,
    output="output.xml",
):
    """
    Takes in an optional path to an xml backup created by SMS Backup and Restore
        (see https://synctech.com.au/sms-backup-restore/).
    Takes in an optional list of filepaths to texts exported from Textra as text
        files.
    Takes in an optional list of phrases to strip if a text matches any of them
        exactly; used for removing meta notifications such as "You sent a picture."
    Takes in an optional flag to toggle fixing MMS.
    Takes in an optional export filepath, defaulting to "output.xml".

    Deduplicates all messages from the provided files and saves it as an xml file
        suitable for use with SMS Backup and Restore.
    """

    # Either read in xml file or create a blank one.
    read_tree = (
        ET.parse(xml_filepath)
        if xml_filepath is not None
        else ET.ElementTree(ET.Element("smses"))
    )

    # Make a new tree to set.
    tree = ET.ElementTree(ET.Element("smses"))

    # Generate lookup table to check for duplicated messages.
    lookup = set()

    # Parse data from files into a list of messages.
    messages = chain(
        (msg for msg in read_tree.getroot()),
        *(parse_textra_file(txt_filepath) for txt_filepath in txt_filepaths)
    )

    # Append and remove duplicates.
    for message in messages:
        if make_lookup_tuple(message) not in lookup:
            lookup.add(make_lookup_tuple(message))
            tree.getroot().append(message)

    # Strip texts based on strip phrases.
    if strip_phrases is not None:
        tree = strip_texts(tree, strip_phrases)

    # Strip invalid address token, if desired.
    if flag_strip_invalid_address:
        tree = strip_invalid_address(tree)

    # Fix sent-from MMS addresses, if desired.
    if flag_fix_sent_from_address:
        tree = fix_sent_from_address(tree)

    # Fix the message count and backup date and output.
    tree.getroot().attrib["count"] = str(len(tree.getroot()))
    tree.getroot().attrib["backup_date"] = str(
        int(datetime.now().timestamp()) * SEC_TO_MS
    )
    with open(output, "w+") as f:
        tree.write(
            f,
            encoding="unicode",
            xml_declaration={
                "version": "1.0",
                "encoding": "UTF-8",
                "standalone": "yes",
            },
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="combine disparate text backup files for restoring"
    )
    parser.add_argument(
        "--xml", type=str, help="filepath of the SMS Backup and Restore xml file"
    )
    parser.add_argument(
        "--textra", type=str, nargs="*", help="filepath to Textra export file(s)"
    )
    parser.add_argument(
        "--strip",
        type=str,
        nargs="*",
        help="remove texts if they match phrase(s) exactly",
    )
    parser.add_argument("--strip-invalid-addr", action="store_true")
    parser.add_argument("--fix-sent-from-addr", action="store_true")
    parser.add_argument("--output", type=str, help="desired filepath to output")
    args = parser.parse_args()
    main(
        xml_filepath=args.xml,
        txt_filepaths=args.textra,
        strip_phrases=args.strip,
        flag_strip_invalid_address=args.strip_invalid_addr,
        flag_fix_sent_from_address=args.fix_sent_from_addr,
        output=args.output,
    )
