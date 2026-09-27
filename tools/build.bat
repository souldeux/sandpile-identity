@echo off
rem Builds tools\sandid.exe with the Visual Studio 2019 C compiler.
call "C:\Program Files (x86)\Microsoft Visual Studio\2019\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
cd /d "%~dp0"
cl /nologo /O2 /W3 /D_CRT_SECURE_NO_WARNINGS sandid.c /Fe:sandid.exe
del sandid.obj 2>nul
