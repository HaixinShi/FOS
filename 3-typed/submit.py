#!/usr/bin/env python3

# This script was contributed by Timothée Loyck Andres.

import argparse
import json
import os.path
import pathlib
import shutil
import ssl
import tempfile
from email import encoders
from email.mime.base import MIMEBase
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from getpass import getpass
from smtplib import SMTP_SSL, SMTPAuthenticationError, SMTPDataError
from typing import List, Optional, Any, Union

# ========================= CONFIG VARIABLES =========================
SMTP_SERVER = 'mail.epfl.ch'
BOT_EMAIL_ADDRESS = 'lamp.fos.bot@gmail.com'

# The minimum number of people in a group
MIN_SCIPERS = 1
# The maximum number of people in a group
MAX_SCIPERS = 3

# The number of the project (set to None to prompt user)
PROJECT_NUMBER = None

# The name of the file in which the submission configuration is stored
CONFIG_FILE_NAME = '.submission_info.json'
# The name of the folder to be zipped
SRC_FOLDER = 'src'
# ====================================================================

project_path = pathlib.Path(__file__).parent.resolve()
config_path = f'{project_path}/{CONFIG_FILE_NAME}'
src_path = f'{project_path}/{SRC_FOLDER}'
tmp_folder = tempfile.gettempdir()


class ConfigData:
    def __init__(self, data_values: Optional[dict] = None, **kwargs):
        """
        Creates a new data object with the given values. A dictionary may be passed, or keyword arguments for each data
        piece.

        Contains: email address, username, SCIPER numbers of the group's members, project number

        :argument data_values: an optional dictionary containing the required data
        :keyword email: the email of the user
        :keyword username: the GASPAR id of the user
        :keyword scipers: the list of SCIPER numbers of the group's members
        :keyword project_num: the project's number
        """
        if data_values is not None:
            data = data_values
        elif len(kwargs) > 0:
            data = kwargs
        else:
            data = dict()

        self.email: str = data.get('email')
        self.username: str = data.get('username')
        self.scipers: List[str] = data.get('scipers')
        self.project_num: int = data.get('project_num')

    def get_config_data(self) -> dict:
        return {
            'email': self.email,
            'username': self.username,
            'scipers': self.scipers,
            'project_num': self.project_num
        }


def get_scipers() -> List:
    """
    Retrieves the group's SCIPER numbers.

    :return: a list containing the SCIPER numbers of all the members of the FoS group
    """

    def is_sciper(string: str) -> bool:
        try:
            return len(string) == 6 and int(string) > 0
        except TypeError:
            return False

    num_scipers = None
    scipers: List[str] = []

    while num_scipers is None:
        num_scipers = get_sanitized_input(
            "Number of people in the group: ",
            int,
            predicate=lambda n: MIN_SCIPERS <= n <= MAX_SCIPERS,
            predicate_error_msg=f"The number of people must be between {MIN_SCIPERS} and {MAX_SCIPERS} included."
        )

    for i in range(num_scipers):
        sciper = None
        while sciper is None:
            sciper = get_sanitized_input(
                f"SCIPER {i + 1}: ",
                predicate=is_sciper,
                predicate_error_msg="Invalid SCIPER number. Please try again."
            )
        scipers.append(sciper)

    return scipers


def get_sanitized_input(prompt: str, value_type: type = str, **kwargs) -> Optional[Any]:
    """
    Sanitizes the user's input.

    :param prompt: the message to be displayed for the user
    :param value_type: the type of value that we expect, for example str or int
    :keyword allow_empty: allow the input to be empty. The returned string may be the empty string
    :keyword predicate: a function that, when applied to the sanitized input, checks if it is valid
    :keyword predicate_error_msg: a message to be displayed if the predicate returns false on the input
    :return: the input as the passed type, or None if the input contained only whitespaces or if the type cast failed
    """
    str_value = input(prompt).strip()
    if len(str_value) > 0 or kwargs.get('allow_empty'):
        try:
            value = value_type(str_value)
            p = kwargs.get('predicate')
            if p is not None and not p(value):
                if kwargs.get('predicate_error_msg') is None:
                    print("Invalid value. Please try again.")
                elif len(kwargs.get('predicate_error_msg')) > 0:
                    print(kwargs.get('predicate_error_msg'))
                return None
            return value
        except TypeError:
            raise TypeError(f"Incorrect value type: {value_type}")
        except ValueError:
            print(f"The value could not be interpreted as type {value_type.__name__}. Please try again.")
    return None


def get_config(from_file: bool = True) -> ConfigData:
    """
    Retrieves the configuration for sending the email. It may be fetched from a configuration file, or if it does not
    exist or is incomplete, it will ask the user for the data, then write it to the config file.

    :param from_file: whether to retrieve the configuration from the config file if it exists. Default is True
    :return: the configuration to use for the email
    """
    data = ConfigData()

    # Set project number if it is already specified
    data.project_num = PROJECT_NUMBER

    if from_file and not os.path.isfile(config_path):
        print('Please provide data that will be used to submit your project.')
        print(f'This information (sans the password) will be saved in: ./{CONFIG_FILE_NAME}')

    if from_file and os.path.isfile(config_path):
        with open(config_path, 'r') as config_file:
            config = json.load(config_file)
        if type(config) is dict:
            data = ConfigData(config)

    if data.scipers is None:
        data.scipers = get_scipers()
    while data.email is None:
        data.email = get_sanitized_input("Email address: ", predicate=lambda address: '@' in address)
    while data.username is None:
        data.username = get_sanitized_input("Gaspar ID: ")
    while data.project_num is None:
        data.project_num = get_sanitized_input("Project number: ", int, predicate=lambda n: n > 0)

    set_config(data)
    return data


def set_config(data: ConfigData) -> None:
    """
    Saves the configuration in the config file.

    :param data: the data to be saved
    """
    with open(config_path, 'w') as config_file:
        json.dump(data.get_config_data(), config_file)


def create_email(frm: str, to: str, subject: str, content: Optional[str] = None,
                 attachments: Optional[Union[str, List[str]]] = None) -> MIMEMultipart:
    """
    Creates an email.

    :param frm: the address from which the email is sent
    :param to: the address to which send the email
    :param subject: the subject of the email
    :param content: the content of the email. Can be empty
    :param attachments: the attachments of the email. Can be a path or a list of paths
    """
    message = MIMEMultipart()
    message['From'] = frm
    message['To'] = to
    message['Subject'] = subject

    if content is not None:
        # Add content into body of message
        message.attach(MIMEText(content, 'plain'))

    if attachments is not None:
        if type(attachments) is str:
            attachments = [attachments]

        for attachment_path in attachments:
            part = MIMEBase("application", "octet-stream")

            with open(attachment_path, 'rb') as attachment:
                part.set_payload(attachment.read())

            encoders.encode_base64(part)
            part.add_header("Content-Disposition", f"attachment; filename={os.path.basename(attachment_path)}")
            message.attach(part)

    return message


if __name__ == '__main__':
    arg_parser = argparse.ArgumentParser(description="Submits the project to the bot for grading.", allow_abbrev=False)
    arg_parser.add_argument('-r', '--reset', action='store_true', help="ask for the submission data even if previously "
                                                                       "specified")
    arg_parser.add_argument('-s', '--self', action='store_true', help="send the mail to yourself instead of the bot")

    if not os.path.isdir(src_path):
        arg_parser.exit(1, f"No {SRC_FOLDER} folder found. Aborting.\n")

    args = arg_parser.parse_args()

    config: ConfigData = get_config(from_file=not args.reset)
    password: str = getpass("Gaspar password: ")

    recipient = config.email if args.self else BOT_EMAIL_ADDRESS

    mail = create_email(
        config.email,
        recipient,
        f"Project {config.project_num} ({', '.join(config.scipers)})",
        attachments=shutil.make_archive(f'{tmp_folder}/{SRC_FOLDER}', 'zip', root_dir=project_path,
                                        base_dir=f'{SRC_FOLDER}')
    )

    with SMTP_SSL(SMTP_SERVER, context=ssl.create_default_context()) as server:
        try:
            server.login(config.username, password)
            server.sendmail(config.email, recipient, mail.as_string())
            print(f"Submission sent to {recipient}.")
        except SMTPAuthenticationError as e:
            if e.smtp_code == 535:
                print(f"Wrong GASPAR ID ({config.username}) or password. Your ID will be asked for again on the next"
                      " run.")

                # Remove (potentially) incorrect ID from config
                config.username = None
                set_config(config)

                exit(2)
            else:
                raise
        except SMTPDataError as e:
            if e.smtp_code == 550:
                print("You email address seems to be incorrect. It will be asked for again on the next run.")

                # Remove incorrect address from config
                config.email = None
                set_config(config)

                exit(2)
            else:
                raise
