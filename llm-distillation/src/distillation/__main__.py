"""Allow ``python -m distillation`` to run the CLI."""

from .cli import main

raise SystemExit(main())
