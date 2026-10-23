SetPackageInfo( rec(

PackageName := "FusionSystems",
Subtitle := "Fusion systems in GAP",
Version := "0.1",
Date := "21/10/2026", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames := "Pete",
    LastName := "Gautam",
    WWWHome := "https://github.com/pete-g00",
    Email := "pratyush.gautam@manchester.ac.uk",
    IsAuthor := true,
    IsMaintainer := true,
    PostalAddress := "Alan Turing Building,\nUniversity of Manchester,\nManchester,\n M13 9PY,\nUnited Kingdom",
    Place := "Manchester",
    Institution := "University of Manchester",
  ),
  rec(
    FirstNames := "Justin",
    LastName := "Lynd",
    WWWHome := "https://userweb.ucs.louisiana.edu/~jxl7583/",
    Email := "lynd@louisiana.edu",
    IsAuthor := true,
    IsMaintainer := false,
    PostalAddress := "Mathematics Department\nUniversity of Louisiana at Lafayette\n217 Maxim Doucet Hall, P.O. Box 43568\nLafayette, LA 70504-3568 USA",
    Place := "Louisiana",
    Institution := "University of Louisiana",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/pete-g00/FusionSystems",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome := "https://pete-g00.github.io/FusionSystems/",
PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL     := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "The FusionSystems package allows for computation with fusion systems. Currently, it supports finding proto-essential subgroups for a given p-group and checking whether it could support reduced fusion systems.",

PackageDoc := rec(
  BookName  := "FusionSystems",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A GAP package on fusion systems",
),

Dependencies := rec(
  GAP := ">= 4.7",
  NeededOtherPackages := [["anupq",">=3.2.1"],["autpgrp",">=1.10.2"],["format",">=1.4.3"],["crisp",">=1.4.5"]],
  SuggestedOtherPackages := [],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",
#Keywords := [ "TODO" ],

AutoDoc := rec(
    entities := rec(
      FUSIONSYSYTEMS := "<Package>FusionSystems</PACKAGE>"
    ),
    TitlePage := rec(
      Copyright := """
      FusionSystems is free software; you can redistribute and/or modify
      it under the terms of the <URL Text="GNU General Public License">
      https://www.fsf.org/licenses/gpl.html</URL> as published by
      the Free Software Foundation; either version 2 of the License, or (at
      your opinion) any later version.
      """,
      Abstract := """
      The FusionSystems package allows for computation with fusion systems. 
      Currently, it supports finding proto-essential subgroups for a given 
      p-group and checking whether it could support reduced fusion systems.
      """,
      Acknowledgements := """
      We thank Martin van Beek for helping expand the list of proto-essential 
      and reduced checks. We also thank David Burrell and Josh Bridges for their 
      contributions to the project.
      """
    )
)

));

