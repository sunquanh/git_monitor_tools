@echo off
title Git Repository Monitor
cd /d "%~dp0"

echo ========================================
echo   Git Repository Monitor - Web Version
echo ========================================
echo.

:: ---- Find Python ----
where python >nul 2>&1
if %errorlevel% neq 0 (
    echo [ERROR] Python not found in PATH
    pause
    exit /b 1
)

for /f "tokens=*" %%i in ('where python') do (
    set PYTHON_PATH=%%i
    goto :found_python
)
:found_python
echo [OK] Python: %PYTHON_PATH%

:: ---- Zero-dependency: routing layer is stdlib http.server, no pip install needed ----

:: ---- Safety-net cleanup from a previous run ----
:: Kill ONLY processes whose command line contains git_web.py.
:: (Never touches unrelated programs; the old blind taskkill-by-port is gone.)
:: NOTE: keep this file pure ASCII - cmd parses .bat with the GBK codepage and
:: UTF-8 Chinese comments break the parser (that is what the '[ERROR]' is not
:: recognized errors were about).
powershell -NoProfile -Command "Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { $_.CommandLine -like '*git_web.py*' } | ForEach-Object { Write-Host ('  [INFO] killed leftover git_web.py PID ' + $_.ProcessId); Stop-Process -Id $_.ProcessId -Force }" 2>nul

echo.
echo [INFO] Starting server...
echo   URL: http://127.0.0.1:8420
echo   Close this window (or press Ctrl+C) to stop the server
echo.

:: ---- Start server (port conflict / zombie detection is inside git_web.py) ----
python -u git_web.py

:: ---- Cleanup after exit: same verified-only kill, in case the server was
:: interrupted mid-run and left a python holding the port ----
echo.
echo [INFO] Server stopped, checking for leftover processes...
powershell -NoProfile -Command "Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { $_.CommandLine -like '*git_web.py*' } | ForEach-Object { Write-Host ('  [INFO] killed leftover git_web.py PID ' + $_.ProcessId); Stop-Process -Id $_.ProcessId -Force }" 2>nul

echo [INFO] Clean. Press any key to close.
pause >nul
