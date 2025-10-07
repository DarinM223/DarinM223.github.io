base_name=$(basename $1)
pandoc --standalone --template template.html $1.md -o $base_name.html