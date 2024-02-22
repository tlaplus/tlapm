-------------- MODULE ENABLEDrewrites_state_level_fingerprint_test -------------

================================================================================
command: cp v1.tla temp.tla
command: ${TLAPM} --toolbox 0 0 temp.tla
stderr: All 2 obligations proved
command: rm -f temp.tla && cp v2.tla temp.tla
command: ${TLAPM} --toolbox 0 0 temp.tla
stderr: obligations failed
command: rm temp.tla
