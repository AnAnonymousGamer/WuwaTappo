# WuWaTappo Automation

A single-file Python script for Windows that starts WuWaTappo, increases the click count, opens chests, and optionally synthesizes items. It uses the app's internal interfaces without moving the mouse. Requires an installed copy of WuWaTappo and only the Python standard library.

## Usage

```powershell
python wuwatappo_auto.py start -a  # Run in the background with automatic synthesis
python wuwatappo_auto.py status    # Show current status
python wuwatappo_auto.py stop      # Stop automation and close WuWaTappo
python wuwatappo_auto.py --help    # Show all options
```

You can close the terminal after `start`ing in the background; use `stop` to shut down. Alternatively, use `run -a` in the foreground and press `Ctrl+C` to stop automation and close the app.

## Options

| Option | Description |
| --- | --- |
| `-a / --auto` | Choose upgrade or same-tier synthesis using collection progress from the latest catalog |
| `-e / --enhance` | Upgrade only: combine 10 items into 1 higher-tier item |
| `-s / --same-tier` | Same-tier only: combine 5 items into 1 item |
| `--cn` | Use the CN variant; not tested |
| `-f / --frequency` | Clicks per second; default `5`, range `0.2-20` |
| `-d / --duration` | Duration in seconds; default `0` runs continuously |
| `-x / --exe` | Specify the path to `WuwaTappo.exe` manually |

`-a`, `-e`, and `-s` are mutually exclusive. Automatic mode prefers upgrades. It uses same-tier synthesis when all higher tiers are complete but the current tier is incomplete, including the highest tier. It stops synthesizing a category once all its tiers are complete.

Synthesis starts 30 seconds after a successful draw. Each step performs one synthesis, with a 30-second interval, until no further synthesis is possible.

## Login and Files

To enable automatic login, create `config.json` beside the script:

```json
{
  "username": "your-account",
  "password": "your-password"
}
```

Automatic login is enabled only when both fields are valid. Password login currently supports the Global variant only; verification challenges or character selection may require manual input.
