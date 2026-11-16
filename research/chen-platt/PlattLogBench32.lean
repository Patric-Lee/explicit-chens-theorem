import PlattLogKernel
namespace ChenEffective.PlattWindow.LogCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option trace.profiler true
set_option trace.profiler.threshold 10
theorem arithmetic_bench_32 :
    [
    (Nat.beq (rationalBounds 4000000 1 21).1 4278927685558894 &&
     Nat.beq (rationalBounds 4000000 1 21).2 4278927685559620 &&
     Nat.beq (rationalBounds 4278927685558894 scale 3).1 766009988848252 &&
     Nat.beq (rationalBounds 4278927685559620 scale 3).2 766009988848432),
    (Nat.beq (rationalBounds 5408448 1 22).1 4363839626598916 &&
     Nat.beq (rationalBounds 5408448 1 22).2 4363839626599675 &&
     Nat.beq (rationalBounds 4363839626598916 scale 3).1 771540938553438 &&
     Nat.beq (rationalBounds 4363839626599675 scale 3).2 771540938553618),
    (Nat.beq (rationalBounds 7133248 1 22).1 4441753165417638 &&
     Nat.beq (rationalBounds 7133248 1 22).2 4441753165418397 &&
     Nat.beq (rationalBounds 4441753165417638 scale 3).1 776522155466580 &&
     Nat.beq (rationalBounds 4441753165418397 scale 3).2 776522155466758),
    (Nat.beq (rationalBounds 9336704 1 23).1 4517522465404512 &&
     Nat.beq (rationalBounds 9336704 1 23).2 4517522465405304 &&
     Nat.beq (rationalBounds 4517522465404512 scale 4).1 781283181090726 &&
     Nat.beq (rationalBounds 4517522465405304 scale 4).2 781283181090941),
    (Nat.beq (rationalBounds 12120640 1 23).1 4590975186043624 &&
     Nat.beq (rationalBounds 12120640 1 23).2 4590975186044416 &&
     Nat.beq (rationalBounds 4590975186043624 scale 4).1 785823018902842 &&
     Nat.beq (rationalBounds 4590975186044416 scale 4).2 785823018903057),
    (Nat.beq (rationalBounds 15723392 1 23).1 4664226165099852 &&
     Nat.beq (rationalBounds 15723392 1 23).2 4664226165100644 &&
     Nat.beq (rationalBounds 4664226165099852 scale 4).1 790278621189948 &&
     Nat.beq (rationalBounds 4664226165100644 scale 4).2 790278621190161),
    (Nat.beq (rationalBounds 20461824 1 24).1 4738369873295546 &&
     Nat.beq (rationalBounds 20461824 1 24).2 4738369873296371 &&
     Nat.beq (rationalBounds 4738369873295546 scale 4).1 794717827347072 &&
     Nat.beq (rationalBounds 4738369873296371 scale 4).2 794717827347285),
    (Nat.beq (rationalBounds 26692224 1 24).1 4813189125550472 &&
     Nat.beq (rationalBounds 26692224 1 24).2 4813189125551297 &&
     Nat.beq (rationalBounds 4813189125550472 scale 4).1 799127615956304 &&
     Nat.beq (rationalBounds 4813189125551297 scale 4).2 799127615956517),
    (Nat.beq (rationalBounds 34519424 1 25).1 4885570385711562 &&
     Nat.beq (rationalBounds 34519424 1 25).2 4885570385712420 &&
     Nat.beq (rationalBounds 4885570385711562 scale 4).1 803328955672914 &&
     Nat.beq (rationalBounds 4885570385712420 scale 4).2 803328955673129),
    (Nat.beq (rationalBounds 44475392 1 25).1 4956900048123914 &&
     Nat.beq (rationalBounds 44475392 1 25).2 4956900048124772 &&
     Nat.beq (rationalBounds 4956900048123914 scale 4).1 807408798575910 &&
     Nat.beq (rationalBounds 4956900048124772 scale 4).2 807408798576125),
    (Nat.beq (rationalBounds 57176832 1 25).1 5027610146553022 &&
     Nat.beq (rationalBounds 57176832 1 25).2 5027610146553880 &&
     Nat.beq (rationalBounds 5027610146553022 scale 4).1 811395665367326 &&
     Nat.beq (rationalBounds 5027610146553880 scale 4).2 811395665367539),
    (Nat.beq (rationalBounds 73523968 1 26).1 5098390594870032 &&
     Nat.beq (rationalBounds 73523968 1 26).2 5098390594870923 &&
     Nat.beq (rationalBounds 5098390594870032 scale 4).1 815330733127216 &&
     Nat.beq (rationalBounds 5098390594870923 scale 4).2 815330733127431),
    (Nat.beq (rationalBounds 94832896 1 26).1 5170027357074544 &&
     Nat.beq (rationalBounds 94832896 1 26).2 5170027357075435 &&
     Nat.beq (rationalBounds 5170027357074544 scale 4).1 819258170285750 &&
     Nat.beq (rationalBounds 5170027357075435 scale 4).2 819258170285963),
    (Nat.beq (rationalBounds 121825280 1 26).1 5240528826222476 &&
     Nat.beq (rationalBounds 121825280 1 26).2 5240528826223367 &&
     Nat.beq (rationalBounds 5240528826222476 scale 4).1 823070589605180 &&
     Nat.beq (rationalBounds 5240528826223367 scale 4).2 823070589605391),
    (Nat.beq (rationalBounds 156240896 1 27).1 5310562934430498 &&
     Nat.beq (rationalBounds 156240896 1 27).2 5310562934431422 &&
     Nat.beq (rationalBounds 5310562934430498 scale 4).1 826807290779672 &&
     Nat.beq (rationalBounds 5310562934431422 scale 4).2 826807290779885),
    (Nat.beq (rationalBounds 200124416 1 27).1 5380239315416268 &&
     Nat.beq (rationalBounds 200124416 1 27).2 5380239315417192 &&
     Nat.beq (rationalBounds 5380239315416268 scale 4).1 830476320465274 &&
     Nat.beq (rationalBounds 5380239315417192 scale 4).2 830476320465487),
    (Nat.beq (rationalBounds 255951360 1 27).1 5449495719262988 &&
     Nat.beq (rationalBounds 255951360 1 27).2 5449495719263912 &&
     Nat.beq (rationalBounds 5449495719262988 scale 4).1 834076447402350 &&
     Nat.beq (rationalBounds 5449495719263912 scale 4).2 834076447402561),
    (Nat.beq (rationalBounds 327841280 1 28).1 5519172643659228 &&
     Nat.beq (rationalBounds 327841280 1 28).2 5519172643660185 &&
     Nat.beq (rationalBounds 5519172643659228 scale 4).1 837652555974670 &&
     Nat.beq (rationalBounds 5519172643660185 scale 4).2 837652555974885),
    (Nat.beq (rationalBounds 419827712 1 28).1 5588785579326930 &&
     Nat.beq (rationalBounds 419827712 1 28).2 5588785579327887 &&
     Nat.beq (rationalBounds 5588785579326930 scale 4).1 841180577160518 &&
     Nat.beq (rationalBounds 5588785579327887 scale 4).2 841180577160731),
    (Nat.beq (rationalBounds 536866816 1 28).1 5658001861157682 &&
     Nat.beq (rationalBounds 536866816 1 28).2 5658001861158639 &&
     Nat.beq (rationalBounds 5658001861157682 scale 4).1 844645192704712 &&
     Nat.beq (rationalBounds 5658001861158639 scale 4).2 844645192704925),
    (Nat.beq (rationalBounds 685934592 1 29).1 5726972301655860 &&
     Nat.beq (rationalBounds 685934592 1 29).2 5726972301656850 &&
     Nat.beq (rationalBounds 5726972301655860 scale 4).1 848055598446444 &&
     Nat.beq (rationalBounds 5726972301656850 scale 4).2 848055598446657),
    (Nat.beq (rationalBounds 875792896 1 29).1 5795749970993576 &&
     Nat.beq (rationalBounds 875792896 1 29).2 5795749970994566 &&
     Nat.beq (rationalBounds 5795749970993576 scale 4).1 851415815299386 &&
     Nat.beq (rationalBounds 5795749970994566 scale 4).2 851415815299599),
    (Nat.beq (rationalBounds 1117878272 1 30).1 5864446225973802 &&
     Nat.beq (rationalBounds 1117878272 1 30).2 5864446225974825 &&
     Nat.beq (rationalBounds 5864446225973802 scale 4).1 854732483418740 &&
     Nat.beq (rationalBounds 5864446225974825 scale 4).2 854732483418953),
    (Nat.beq (rationalBounds 1428151296 1 30).1 5933393048422418 &&
     Nat.beq (rationalBounds 1428151296 1 30).2 5933393048423441 &&
     Nat.beq (rationalBounds 5933393048422418 scale 4).1 858022412316228 &&
     Nat.beq (rationalBounds 5933393048423441 scale 4).2 858022412316439),
    (Nat.beq (rationalBounds 1823263744 1 30).1 6002142566463676 &&
     Nat.beq (rationalBounds 1823263744 1 30).2 6002142566464699 &&
     Nat.beq (rationalBounds 6002142566463676 scale 4).1 861265079194854 &&
     Nat.beq (rationalBounds 6002142566464699 scale 4).2 861265079195067),
    (Nat.beq (rationalBounds 2326419456 1 31).1 6070738640465180 &&
     Nat.beq (rationalBounds 2326419456 1 31).2 6070738640466236 &&
     Nat.beq (rationalBounds 6070738640465180 scale 4).1 864463700266440 &&
     Nat.beq (rationalBounds 6070738640466236 scale 4).2 864463700266653),
    (Nat.beq (rationalBounds 2967246848 1 31).1 6139222674426154 &&
     Nat.beq (rationalBounds 2967246848 1 31).2 6139222674427210 &&
     Nat.beq (rationalBounds 6139222674426154 scale 4).1 867621244097010 &&
     Nat.beq (rationalBounds 6139222674427210 scale 4).2 867621244097221),
    (Nat.beq (rationalBounds 3783396352 1 31).1 6207617596819120 &&
     Nat.beq (rationalBounds 3783396352 1 31).2 6207617596820176 &&
     Nat.beq (rationalBounds 6207617596819120 scale 4).1 870739719056306 &&
     Nat.beq (rationalBounds 6207617596820176 scale 4).2 870739719056521),
    (Nat.beq (rationalBounds 4824619008 1 32).1 6276046882020040 &&
     Nat.beq (rationalBounds 4824619008 1 32).2 6276046882021129 &&
     Nat.beq (rationalBounds 6276046882020040 scale 4).1 873825563666578 &&
     Nat.beq (rationalBounds 6276046882021129 scale 4).2 873825563666791),
    (Nat.beq (rationalBounds 6153265152 1 32).1 6344515977012388 &&
     Nat.beq (rationalBounds 6153265152 1 32).2 6344515977013477 &&
     Nat.beq (rationalBounds 6344515977012388 scale 4).1 876879710492936 &&
     Nat.beq (rationalBounds 6344515977013477 scale 4).2 876879710493151),
    (Nat.beq (rationalBounds 7845230592 1 32).1 6412892700063966 &&
     Nat.beq (rationalBounds 7845230592 1 32).2 6412892700065055 &&
     Nat.beq (rationalBounds 6412892700063966 scale 4).1 879897019307904 &&
     Nat.beq (rationalBounds 6412892700065055 scale 4).2 879897019308117),
    (Nat.beq (rationalBounds 10000000000 1 33).1 6481200854247642 &&
     Nat.beq (rationalBounds 10000000000 1 33).2 6481200854248764 &&
     Nat.beq (rationalBounds 6481200854247642 scale 4).1 882879348526828 &&
     Nat.beq (rationalBounds 6481200854248764 scale 4).2 882879348527041)].all (fun b => b) = true := by
  decide +kernel
#print axioms arithmetic_bench_32
end ChenEffective.PlattWindow.LogCertificate
