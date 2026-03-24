from __future__ import annotations

import os
import smtplib
import socket
from dataclasses import dataclass
from datetime import datetime
from email.message import EmailMessage
from pathlib import Path

import tomllib

DEFAULT_CONFIG_PATH = Path("email_config.toml")
EMAIL_CONFIG_ENV = "EMAIL_CONFIG_PATH"
EMAIL_SECTION = "email"
REQUIRED_EMAIL_KEYS = (
    "smtp_server",
    "smtp_port",
    "sender_email",
    "sender_password",
    "receiver_email",
)


@dataclass(frozen=True)
class EmailConfig:
    smtp_server: str
    smtp_port: int
    sender_email: str
    sender_password: str
    receiver_email: str


def _resolve_config_path(path: str | Path | None) -> Path:
    if path is not None:
        return Path(path)
    return Path(os.getenv(EMAIL_CONFIG_ENV) or DEFAULT_CONFIG_PATH)


def load_email_config(path: str | Path = DEFAULT_CONFIG_PATH) -> EmailConfig:
    config_path = Path(path)
    data = tomllib.loads(config_path.read_text(encoding="utf-8"))
    section = data.get(EMAIL_SECTION, data)
    if not isinstance(section, dict):
        raise ValueError(f"Invalid [{EMAIL_SECTION}] section in {config_path}")

    missing = [key for key in REQUIRED_EMAIL_KEYS if key not in section]
    if missing:
        raise ValueError(f"Missing email config keys: {', '.join(missing)}")

    return EmailConfig(
        smtp_server=str(section["smtp_server"]),
        smtp_port=int(section["smtp_port"]),
        sender_email=str(section["sender_email"]),
        sender_password=str(section["sender_password"]),
        receiver_email=str(section["receiver_email"]),
    )


def send_email(subject: str, body: str, config_path: str | Path | None = None) -> bool:
    try:
        config = load_email_config(_resolve_config_path(config_path))
    except Exception as exc:
        print(f"[email] failed to load config: {exc}")
        return False

    message = EmailMessage()
    message["From"] = config.sender_email
    message["To"] = config.receiver_email
    message["Subject"] = subject
    message.set_content(body)

    try:
        with smtplib.SMTP_SSL(config.smtp_server, config.smtp_port) as server:
            server.login(config.sender_email, config.sender_password)
            server.send_message(message)
    except Exception as exc:
        print(f"[email] failed to send: {exc}")
        return False

    print("[email] sent notification.")
    return True


def _build_pipeline_body(
    *,
    intro: str,
    lean_dir: str,
    run_log_dir: str | Path,
    fields: list[str],
    details_label: str | None = None,
    details: str | None = None,
) -> str:
    body_lines = [
        intro,
        "",
        f"time: {datetime.now().astimezone().isoformat(timespec='seconds')}",
        f"host: {socket.gethostname()}",
        f"cwd: {Path.cwd()}",
        f"lean_dir: {lean_dir}",
        f"run_log_dir: {Path(run_log_dir).resolve()}",
        *fields,
    ]
    if details:
        body_lines.extend(["", details_label or "details:", details])
    return "\n".join(body_lines)


def send_pipeline_codex_failure_email(
    reason: str,
    *,
    lean_dir: str,
    run_log_dir: str | Path,
    details: str | None = None,
    config_path: str | Path | None = None,
) -> bool:
    subject = f"[pipeline] codex failure in {lean_dir}"
    body = _build_pipeline_body(
        intro="The pipeline stopped because of a codex-related failure.",
        lean_dir=lean_dir,
        run_log_dir=run_log_dir,
        fields=[f"reason: {reason}"],
        details=details,
    )
    return send_email(subject=subject, body=body, config_path=config_path)


def send_pipeline_completion_email(
    *,
    lean_dir: str,
    run_log_dir: str | Path,
    build_ok: bool,
    config_path: str | Path | None = None,
) -> bool:
    build_status = "success" if build_ok else "fail"
    subject = f"[pipeline] completed in {lean_dir} ({build_status})"
    body = _build_pipeline_body(
        intro="The pipeline processed all paths successfully and then ran lake build.",
        lean_dir=lean_dir,
        run_log_dir=run_log_dir,
        fields=[f"build_status: {build_status}"],
    )
    return send_email(subject=subject, body=body, config_path=config_path)
