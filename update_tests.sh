#!/bin/bash

PATTERN=$1

# First create the directory structure to prevent copy errors
TESTS=( $(find sv-tests -type d) )
TESTS+=( $(find uvm -type d) )

for dir in ${TESTS[@]}; do
    mkdir -p test/corpus/$dir
done

# Retrieve all the test files
FILES_SV=( $(find sv-tests -type f -name "*.sv") )
FILES_SV+=( $(find sv-tests -type f -name "*.svh") )
FILES_SV+=( $(find uvm -type f -name "*.sv") )
FILES_SV+=( $(find uvm -type f -name "*.svh") )

# Declare variables
DIR_FILENAME=
BASE_FILENAME=
FILENAME_NO_EXT=
DEST_FILE=
LAST_FILE_LINE=

# Expected failure tests
EXPECTED_FAIL_FILELIST=(sv-tests/chapter-5/5.6--wrong-identifiers.sv
                        sv-tests/chapter-5/5.7.1--integers-signed-illegal.sv
                        sv-tests/chapter-5/5.7.1--integers-unsized-illegal.sv
                        sv-tests/chapter-5/5.7.2-real-constants-illegal.sv
                        sv-tests/chapter-5/5.10-structure-arrays-illegal.sv
                        # Chapter 6
                        sv-tests/chapter-6/6.9.2--vector_vectored_inv.sv
                        # Chapter 11
                        sv-tests/chapter-11/11.3.6--assign_in_expr_inv.sv
                        # Chapter 22
                        sv-tests/chapter-22/22.11--pragma-invalid.sv
                        sv-tests/chapter-22/22.12--line-illegal-1.sv
                        sv-tests/chapter-22/22.12--line-illegal-2.sv
                        sv-tests/chapter-22/22.12--line-illegal-3.sv
                        sv-tests/chapter-22/22.12--line-illegal-4.sv
                        sv-tests/chapter-22/22.12--line-illegal-5.sv
                        sv-tests/chapter-22/22.5.1--define-expansion_21.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-1.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-2.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-3.sv
                        sv-tests/sanity.sv
                       )

# Exclude tests
EXCLUDED_FILELIST=(sv-tests/chapter-5/5.6.4--compiler-directives-preprocessor-macro_0.sv # No intention of supporting preprocessing
                   sv-tests/chapter-5/5.10-structure-arrays-illegal.sv                   # No intention of detecting the /* C-like assignment is illegal */ for struct initialization
                   sv-tests/chapter-11/11.4.14.3--unpack_stream_inv.sv                   # No intention of parse the width of the streaming assignment target
                   sv-tests/chapter-22/22.5.1--define-expansion_20.sv                    # No intention of supporting parsing of macro expansion
                   sv-tests/chapter-22/22.5.1--define-expansion_25.sv                    # No intention of supporting parsing of macro expansion of string values
                   # No intention of supporting expansion with ifdef/ifndef
                   sv-tests/generic/preproc/preproc_test_2.sv
                   sv-tests/generic/typedef/typedef_test_26.sv
                   sv-tests/generic/typedef/typedef_test_27.sv
                  )


# Filter tests, if there was an argument provided
if [[ -n "$PATTERN" ]]; then
    FILES_SV=( $( printf '%s\n' "${FILES_SV[@]}" | grep "$PATTERN" ) )
    echo "Filtering with regexp: $PATTERN"
fi

# Create tests
for file in "${FILES_SV[@]}"; do
    DIR_FILENAME=$(dirname $file)
    BASE_FILENAME=$(basename $file)
    FILENAME_NO_EXT=${BASE_FILENAME%.sv}
    DEST_FILE=test/corpus/$DIR_FILENAME/${FILENAME_NO_EXT}.txt

    if [[ "${EXCLUDED_FILELIST[@]}" =~ "$file" ]]; then
        echo "Excluding $file ..."
        cat $file > $DEST_FILE
    else
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
    fi

done

