# json2dir-koka

json2dir in Koka: reads a JSON document on stdin and creates the directory tree it describes in the current directory.

    koka -O2 -o out/json2dir json2dir.kk && out/json2dir < tree.json
