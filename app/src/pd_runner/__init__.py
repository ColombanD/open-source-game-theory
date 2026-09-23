"""pd_runner package."""

# Load app/.env into os.environ before anything constructs an Anthropic client
# (which reads ANTHROPIC_API_KEY at construction time). Importing here covers
# every entry point — pd-serve, run-matchup, the eval harness, and ad-hoc
# `python -c "import pd_runner..."` — without touching call sites.
# See dotenv.py for why the key is not exported globally from the shell.
from pd_runner.dotenv import load_dotenv as _load_dotenv

_load_dotenv()
