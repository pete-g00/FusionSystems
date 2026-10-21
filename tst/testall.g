LoadPackage("FusionSystems");

TestDirectory(
    DirectoriesPackageLibrary("FusionSystems", "tst"), 
    rec(
        exitGAP := true,
        testOptions := rec(compareFunction := "uptowhitespace")
    )
);

FORCE_QUIT_GAP(1);