if (Test-Path "handin.zip") {
    Remove-Item "handin.zip"
}
Compress-Archive -Path "./*" -DestinationPath "handin.zip"  -Exclude ".git" -Exclude "src/__pycache__" -Exclude "tests"
