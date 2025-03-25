dune clean
rm -rf *.zip
zip -r artifact.zip . -x ".github/*" ".git/*" ship.sh .DS_Store .gitignore