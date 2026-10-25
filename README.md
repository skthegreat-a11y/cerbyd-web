# Cerbyd Web 5.5.0 — Free Access Release

Cerbyd Web is available without sign-in, account creation, OAuth setup, or payment. This release removes the visible sign-in interface and keeps the existing portal, search, tools, safety responses, and math-answer improvements.

## Run locally on Windows

Open PowerShell in this folder and run:

```powershell
python -m pip install -r requirements.txt
python -m uvicorn main:app --reload --host 127.0.0.1 --port 8000
```

Open http://127.0.0.1:8000/.

## Upgrade notes

- Back up the existing `Documents\cerbyd-web` folder first.
- Replace `main.py`, `index.html`, `requirements.txt`, and the example README files with the files in this package.
- Keep your existing `cerbyd.db` and `.env` file. OAuth credentials are not needed for normal browsing.
- No payment gateway, account, or subscription is required to use the site.
- The backend's legacy authentication routes may remain in the source for compatibility, but the website no longer exposes sign-in or requires a user account to browse.
- Safety detection is a best-effort keyword screen, not a clinical assessment or emergency service. Test it carefully before public deployment.
