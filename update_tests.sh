#!/bin/bash

# First create the directory structure to prevent copy errors
TESTS=( $(find sv-tests -type d) )

for dir in ${TESTS[@]}; do
    mkdir -p test/corpus/$dir
done

# Retrieve all the test files
FILES_SV=( $(find sv-tests -type f -name "*.sv") )
FILES_SVH=( $(find sv-tests -type f -name "*.svh") )

# Declare variables
DIR_FILENAME=
BASE_FILENAME=
FILENAME_NO_EXT=
DEST_FILE=
LAST_FILE_LINE=

# Expected failure tests
EXPECTED_FAIL_FILELIST=(test/corpus/sv-tests/chapter-5/5.7.1--integers-signed-illegal.sv
                        test/corpus/sv-tests/chapter-5/5.7.1--integers-unsized-illegal.sv
                        test/corpus/sv-tests/chapter-5/5.7.2-real-constants-illegal.sv
                        test/corpus/sv-tests/chapter-5/5.10-structure-arrays-illegal.sv)

# Create tests
for file in ${FILES_SV[@]}; do
    DIR_FILENAME=$(dirname $file)
    BASE_FILENAME=$(basename $file)
    FILENAME_NO_EXT=${BASE_FILENAME%.sv}
    DEST_FILE=test/corpus/$DIR_FILENAME/${FILENAME_NO_EXT}.txt

    echo "============================================" > $DEST_FILE
    echo "$DIR_FILENAME/$FILENAME_NO_EXT" >> $DEST_FILE
    [[ "${EXPECTED_FAIL_FILELIST[@]}" =~ "$file" ]] && echo ":error" >> $DEST_FILE
    echo "============================================" >> $DEST_FILE
    echo "" >> $DEST_FILE

    cat $file >> $DEST_FILE
    echo "" >> $DEST_FILE
    echo "----" >> $DEST_FILE
    echo "" >> $DEST_FILE

    tree-sitter parse $file >> $DEST_FILE
    sed -i -E 's/ \[[0-9]+, [0-9]+\] - \[[0-9]+, [0-9]+\]//g' $DEST_FILE # Remove brackets with node positions

    # Check if file has errors and reformat expected file in that case (remove last line)
    LAST_FILE_LINE=$(tail -1 $DEST_FILE | grep -E 'ERROR|MISSING')
    if [[ $LAST_FILE_LINE ]]; then
        # Remove last file line before formatting
        sed -i '$ d' $DEST_FILE
        # Set new last file line without statistics
        LAST_FILE_LINE=$(echo $LAST_FILE_LINE | cut -d " " -f 6-)
        echo "" >> $DEST_FILE
        echo "$LAST_FILE_LINE" >> $DEST_FILE
    fi

    echo "Updated $DEST_FILE"
done

