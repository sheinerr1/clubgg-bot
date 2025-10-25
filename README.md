# ClubGG Poker Bot 🎲

Multi-user Telegram bot for monitoring poker tables across multiple poker sites.

## Features

- **Multi-user support** - Multiple users can manage their own poker sources
- **Group-aware** - Sources can be bound to groups, accessible to all members
- **Multi-site support** - Monitor tables on:
  - ClubGG
  - EBPoker (Diamond)
  - FishPoker
- **Automatic checking** - Customizable intervals per source (1-1440 minutes)
- **Google Sheets integration** - Read poker schedule from shared Google Sheets
- **Browser automation** - Playwright-based table scraping
- **Live tracking** - Count live players vs bots
- **Icons/Text mode** - Toggle between emoji indicators and text

## Setup

### Requirements
- Python 3.10+
- Telegram Bot Token
- Google Sheets API credentials
- Poker site accounts

### Installation

1. Clone repository:
```bash
git clone <your-repo-url>
cd clubgg-bot
```

2. Create virtual environment:
```bash
python -m venv .venv
.venv\Scripts\activate
```

3. Install dependencies:
```bash
pip install -r requirements.txt
```

4. Create `.env` file:
```
TG_TOKEN=your_telegram_bot_token
GG_LOGIN=your_username
GG_PASSWORD=your_password
EBP_LOGIN=your_username
EBP_PASSWORD=your_password
FISH_LOGIN=your_username
FISH_PASSWORD=your_password
TZ=Europe/Moscow
HEADFUL=0
```

5. Run bot:
```bash
python multiuser_bot.py
```

## Commands

### Setup
- `/setup` - Interactive setup wizard for adding sources
- `/list` - Show all your sources
- `/del <id>` - Delete source

### Management
- `/check [id/name]` - Manual check (doesn't affect schedule)
- `/interval <minutes>` - Set interval for all sources
- `/interval <id> <minutes>` - Set interval for specific source
- `/toggle <id>` - Enable/disable source
- `/icons` - Toggle emoji/text mode
- `/refresh` - Refresh browser sessions

### Group Features
- `/setgroup` - Bind sources to group
- `/setgroup disable` - Unbind from group

## How It Works

1. **Source Setup** - Add poker table with UID and Google Sheets schedule
2. **Auto-checking** - Bot checks table at set intervals
3. **Report Generation** - Compares actual vs planned bots
4. **Status Notification** - Sends Telegram message with results

## Database

Sources stored in SQLite with:
- Source info (site, name, UID)
- User credentials (per user per site)
- Intervals and last check time
- Group binding

## Notes

- Each user has separate credentials per site
- Group sources use owner's credentials
- Minimum interval: 1 minute
- Maximum interval: 1440 minutes (24 hours)
- Check time resets when interval changes

## License

Private bot - for personal use only
