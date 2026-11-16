import PlattAssemblyKernel
import PlattCertificates.Count131072.C011472
import PlattCertificates.Count131072.C011473
import PlattCertificates.Count131072.C011474
import PlattCertificates.Count131072.C011475
import PlattCertificates.Count131072.C011476
import PlattCertificates.Count131072.C011477
import PlattCertificates.Count131072.C011478
import PlattCertificates.Count131072.C011479
import PlattCertificates.Count131072.C011480
import PlattCertificates.Count131072.C011481
import PlattCertificates.Count131072.C011482
import PlattCertificates.Count131072.C011483
import PlattCertificates.Count131072.C011484
import PlattCertificates.Count131072.C011485
import PlattCertificates.Count131072.C011486
import PlattCertificates.Count131072.C011487
import PlattCertificates.Count131072.C011488
import PlattCertificates.Count131072.C011489
import PlattCertificates.Count131072.C011490
import PlattCertificates.Count131072.C011491
import PlattCertificates.Count131072.C011492
import PlattCertificates.Count131072.C011493
import PlattCertificates.Count131072.C011494
import PlattCertificates.Count131072.C011495
import PlattCertificates.Count131072.C011496
import PlattCertificates.Count131072.C011497
import PlattCertificates.Count131072.C011498
import PlattCertificates.Count131072.C011499
import PlattCertificates.Count131072.C011500
import PlattCertificates.Count131072.C011501
import PlattCertificates.Count131072.C011502
import PlattCertificates.Count131072.C011503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11472 : List PrefixCut := [⟨45,406824293,406824613⟩,
⟨92,831932162,831932821⟩,
⟨128,1153974469,1153975385⟩]
theorem checked11472 : checkPrefixCuts (2^48) 1507590145 9 Manual.Count131072.C011472.packed 128 cuts11472 = true := by
 decide +kernel
def pointBounds11472 : List (Nat × Nat × Nat) := [(1507636224,92728639159772,92729014631884),(1507684352,92729064267641,92729439740092)]
theorem point_links_checked11472 : (cuts11472.take 2).map (fun c => (1507590145-1+2*2^9*c.k,92728232335479+c.lower,92728607807271+c.upper)) = pointBounds11472 := by
 decide +kernel
def cuts11473 : List PrefixCut := [⟨11,100624961,100625042⟩,
⟨58,527759154,527759573⟩,
⟨105,957119958,957120715⟩,
⟨128,1166755050,1166755970⟩]
theorem checked11473 : checkPrefixCuts (2^48) 1507721217 9 Manual.Count131072.C011473.packed 128 cuts11473 = true := by
 decide +kernel
def pointBounds11473 : List (Nat × Nat × Nat) := [(1507732480,92729486934909,92729862407698),(1507780608,92729914069102,92730289542229),(1507828736,92730343429906,92730718903371)]
theorem point_links_checked11473 : (cuts11473.take 3).map (fun c => (1507721217-1+2*2^9*c.k,92729386309948+c.lower,92729761782656+c.upper)) = pointBounds11473 := by
 decide +kernel
def cuts11474 : List PrefixCut := [⟨24,215231857,215232028⟩,
⟨71,642885253,642885759⟩,
⟨118,1066045129,1066045969⟩,
⟨128,1156200507,1156201419⟩]
theorem checked11474 : checkPrefixCuts (2^48) 1507852289 9 Manual.Count131072.C011474.packed 128 cuts11474 = true := by
 decide +kernel
def pointBounds11474 : List (Nat × Nat × Nat) := [(1507876864,92730768296855,92731143770654),(1507924992,92731195950251,92731571424385),(1507973120,92731619110127,92731994584595)]
theorem point_links_checked11474 : (cuts11474.take 3).map (fun c => (1507852289-1+2*2^9*c.k,92730553064998+c.lower,92730928538626+c.upper)) = pointBounds11474 := by
 decide +kernel
def cuts11475 : List PrefixCut := [⟨37,338030553,338030819⟩,
⟨84,760230231,760230834⟩,
⟨128,1162632675,1162633594⟩]
theorem checked11475 : checkPrefixCuts (2^48) 1507983361 9 Manual.Count131072.C011475.packed 128 cuts11475 = true := by
 decide +kernel
def pointBounds11475 : List (Nat × Nat × Nat) := [(1508021248,92732047296058,92732422770864),(1508069376,92732469495736,92732844970879)]
theorem point_links_checked11475 : (cuts11475.take 2).map (fun c => (1507983361-1+2*2^9*c.k,92731709265505+c.lower,92732084740045+c.upper)) = pointBounds11475 := by
 decide +kernel
def cuts11476 : List PrefixCut := [⟨3,26502889,26502909⟩,
⟨50,458007397,458007756⟩,
⟨97,880353248,880353943⟩,
⟨128,1169623592,1169624516⟩]
theorem checked11476 : checkPrefixCuts (2^48) 1508114433 9 Manual.Count131072.C011476.packed 128 cuts11476 = true := by
 decide +kernel
def pointBounds11476 : List (Nat × Nat × Nat) := [(1508117504,92732898401069,92733273876548),(1508165632,92733329905577,92733705381395),(1508213760,92733752251428,92734127727582)]
theorem point_links_checked11476 : (cuts11476.take 3).map (fun c => (1508114433-1+2*2^9*c.k,92732871898180+c.lower,92733247373639+c.upper)) = pointBounds11476 := by
 decide +kernel
def cuts11477 : List PrefixCut := [⟨16,149111790,149111908⟩,
⟨63,574603251,574603704⟩,
⟨110,991870126,991870906⟩,
⟨128,1156832450,1156833363⟩]
theorem checked11477 : checkPrefixCuts (2^48) 1508245505 9 Manual.Count131072.C011477.packed 128 cuts11477 = true := by
 decide +kernel
def pointBounds11477 : List (Nat × Nat × Nat) := [(1508261888,92734190633562,92734566110063),(1508310016,92734616125023,92734991601859),(1508358144,92735033391898,92735408869061)]
theorem point_links_checked11477 : (cuts11477.take 3).map (fun c => (1508245505-1+2*2^9*c.k,92734041521772+c.lower,92734416998155+c.upper)) = pointBounds11477 := by
 decide +kernel
def cuts11478 : List PrefixCut := [⟨29,268525996,268526210⟩,
⟨76,692483890,692484442⟩,
⟨123,1129676491,1129677385⟩,
⟨128,1170353529,1170354456⟩]
theorem checked11478 : checkPrefixCuts (2^48) 1508376577 9 Manual.Count131072.C011478.packed 128 cuts11478 = true := by
 decide +kernel
def pointBounds11478 : List (Nat × Nat × Nat) := [(1508406272,92735466880218,92735842357728),(1508454400,92735890838112,92736266315960),(1508502528,92736328030713,92736703508903)]
theorem point_links_checked11478 : (cuts11478.take 3).map (fun c => (1508376577-1+2*2^9*c.k,92735198354222+c.lower,92735573831518+c.upper)) = pointBounds11478 := by
 decide +kernel
def cuts11479 : List PrefixCut := [⟨42,378962036,378962335⟩,
⟨89,800080656,800081291⟩,
⟨128,1166146437,1166147361⟩]
theorem checked11479 : checkPrefixCuts (2^48) 1508507649 9 Manual.Count131072.C011479.packed 128 cuts11479 = true := by
 decide +kernel
def pointBounds11479 : List (Nat × Nat × Nat) := [(1508550656,92736747669787,92737123148309),(1508598784,92737168788407,92737544267265)]
theorem point_links_checked11479 : (cuts11479.take 2).map (fun c => (1508507649-1+2*2^9*c.k,92736368707751+c.lower,92736744185974+c.upper)) = pointBounds11479 := by
 decide +kernel
def cuts11480 : List PrefixCut := [⟨8,69592425,69592481⟩,
⟨55,500945403,500945799⟩,
⟨102,911576022,911576743⟩,
⟨128,1156530359,1156531274⟩]
theorem checked11480 : checkPrefixCuts (2^48) 1508638721 9 Manual.Count131072.C011480.packed 128 cuts11480 = true := by
 decide +kernel
def pointBounds11480 : List (Nat × Nat × Nat) := [(1508646912,92737604446613,92737979925816),(1508695040,92738035799591,92738411279134),(1508743168,92738446430210,92738821910078)]
theorem point_links_checked11480 : (cuts11480.take 3).map (fun c => (1508638721-1+2*2^9*c.k,92737534854188+c.lower,92737910333335+c.upper)) = pointBounds11480 := by
 decide +kernel
def cuts11481 : List PrefixCut := [⟨21,188983117,188983268⟩,
⟨68,613765653,613766139⟩,
⟨115,1045623367,1045624195⟩,
⟨128,1159974719,1159975639⟩]
theorem checked11481 : checkPrefixCuts (2^48) 1508769793 9 Manual.Count131072.C011481.packed 128 cuts11481 = true := by
 decide +kernel
def pointBounds11481 : List (Nat × Nat × Nat) := [(1508791296,92738880367664,92739255847877),(1508839424,92739305150200,92739680630748),(1508887552,92739737007914,92740112488804)]
theorem point_links_checked11481 : (cuts11481.take 3).map (fun c => (1508769793-1+2*2^9*c.k,92738691384547+c.lower,92739066864609+c.upper)) = pointBounds11481 := by
 decide +kernel
def cuts11482 : List PrefixCut := [⟨34,308165456,308165703⟩,
⟨81,723207441,723208016⟩,
⟨128,1148308618,1148309530⟩]
theorem checked11482 : checkPrefixCuts (2^48) 1508900865 9 Manual.Count131072.C011482.packed 128 cuts11482 = true := by
 decide +kernel
def pointBounds11482 : List (Nat × Nat × Nat) := [(1508935680,92740159524722,92740535005951),(1508983808,92740574566707,92740950048264),(1509031936,92740999667884,92741375149778)]
theorem point_links_checked11482 : (cuts11482.take 3).map (fun c => (1508900865-1+2*2^9*c.k,92739851359266+c.lower,92740226840248+c.upper)) = pointBounds11482 := by
 decide +kernel
def cuts11483 : List PrefixCut := [⟨47,415388510,415388836⟩,
⟨94,843820012,843820678⟩,
⟨128,1144105516,1144106420⟩]
theorem checked11483 : checkPrefixCuts (2^48) 1509031937 9 Manual.Count131072.C011483.packed 128 cuts11483 = true := by
 decide +kernel
def pointBounds11483 : List (Nat × Nat × Nat) := [(1509080064,92741415056394,92741790538614),(1509128192,92741843487896,92742218970456)]
theorem point_links_checked11483 : (cuts11483.take 2).map (fun c => (1509031937-1+2*2^9*c.k,92740999667884+c.lower,92741375149778+c.upper)) = pointBounds11483 := by
 decide +kernel
def cuts11484 : List PrefixCut := [⟨13,120112288,120112384⟩,
⟨60,541802277,541802707⟩,
⟨107,957510753,957511510⟩,
⟨128,1143446951,1143447856⟩]
theorem checked11484 : checkPrefixCuts (2^48) 1509163009 9 Manual.Count131072.C011484.packed 128 cuts11484 = true := by
 decide +kernel
def pointBounds11484 : List (Nat × Nat × Nat) := [(1509176320,92742263885688,92742639368582),(1509224448,92742685575677,92743061058905),(1509272576,92743101284153,92743476767708)]
theorem point_links_checked11484 : (cuts11484.take 3).map (fun c => (1509163009-1+2*2^9*c.k,92742143773400+c.lower,92742519256198+c.upper)) = pointBounds11484 := by
 decide +kernel
def cuts11485 : List PrefixCut := [⟨26,233675420,233675603⟩,
⟨73,651035882,651036390⟩,
⟨120,1073417978,1073418822⟩,
⟨128,1145771710,1145772612⟩]
theorem checked11485 : checkPrefixCuts (2^48) 1509294081 9 Manual.Count131072.C011485.packed 128 cuts11485 = true := by
 decide +kernel
def pointBounds11485 : List (Nat × Nat × Nat) := [(1509320704,92743520895771,92743896379657),(1509368832,92743938256233,92744313740444),(1509416960,92744360638329,92744736122876)]
theorem point_links_checked11485 : (cuts11485.take 3).map (fun c => (1509294081-1+2*2^9*c.k,92743287220351+c.lower,92743662704054+c.upper)) = pointBounds11485 := by
 decide +kernel
def cuts11486 : List PrefixCut := [⟨39,339945269,339945537⟩,
⟨86,765470408,765471008⟩,
⟨128,1148655288,1148656192⟩]
theorem checked11486 : checkPrefixCuts (2^48) 1509425153 9 Manual.Count131072.C011486.packed 128 cuts11486 = true := by
 decide +kernel
def pointBounds11486 : List (Nat × Nat × Nat) := [(1509465088,92744772937330,92745148422203),(1509513216,92745198462469,92745573947674)]
theorem point_links_checked11486 : (cuts11486.take 2).map (fun c => (1509425153-1+2*2^9*c.k,92744432992061+c.lower,92744808476666+c.upper)) = pointBounds11486 := by
 decide +kernel
def cuts11487 : List PrefixCut := [⟨5,46615421,46615458⟩,
⟨52,475842598,475842976⟩,
⟨99,903378015,903378731⟩,
⟨128,1164218242,1164219165⟩]
theorem checked11487 : checkPrefixCuts (2^48) 1509556225 9 Manual.Count131072.C011487.packed 128 cuts11487 = true := by
 decide +kernel
def pointBounds11487 : List (Nat × Nat × Nat) := [(1509561344,92745628262770,92746003748316),(1509609472,92746057489947,92746432975834),(1509657600,92746485025364,92746860511589)]
theorem point_links_checked11487 : (cuts11487.take 3).map (fun c => (1509556225-1+2*2^9*c.k,92745581647349+c.lower,92745957132858+c.upper)) = pointBounds11487 := by
 decide +kernel
def cuts11488 : List PrefixCut := [⟨18,162020428,162020559⟩,
⟨65,583562446,583562912⟩,
⟨112,1006582544,1006583344⟩,
⟨128,1152184870,1152185784⟩]
theorem checked11488 : checkPrefixCuts (2^48) 1509687297 9 Manual.Count131072.C011488.packed 128 cuts11488 = true := by
 decide +kernel
def pointBounds11488 : List (Nat × Nat × Nat) := [(1509705728,92746907886019,92747283372582),(1509753856,92747329428037,92747704914935),(1509801984,92747752448135,92748127935367)]
theorem point_links_checked11488 : (cuts11488.take 3).map (fun c => (1509687297-1+2*2^9*c.k,92746745865591+c.lower,92747121352023+c.upper)) = pointBounds11488 := by
 decide +kernel
def cuts11489 : List PrefixCut := [⟨31,284674994,284675222⟩,
⟨78,694804970,694805523⟩,
⟨125,1118903087,1118903974⟩,
⟨128,1145746651,1145747558⟩]
theorem checked11489 : checkPrefixCuts (2^48) 1509818369 9 Manual.Count131072.C011489.packed 128 cuts11489 = true := by
 decide +kernel
def pointBounds11489 : List (Nat × Nat × Nat) := [(1509850112,92748182725455,92748558213029),(1509898240,92748592855431,92748968343330),(1509946368,92749016953548,92749392441781)]
theorem point_links_checked11489 : (cuts11489.take 3).map (fun c => (1509818369-1+2*2^9*c.k,92747898050461+c.lower,92748273537807+c.upper)) = pointBounds11489 := by
 decide +kernel
def cuts11490 : List PrefixCut := [⟨44,398918862,398919181⟩,
⟨91,810314491,810315139⟩,
⟨128,1146020088,1146021001⟩]
theorem checked11490 : checkPrefixCuts (2^48) 1509949441 9 Manual.Count131072.C011490.packed 128 cuts11490 = true := by
 decide +kernel
def pointBounds11490 : List (Nat × Nat × Nat) := [(1509994496,92749442715974,92749818204546),(1510042624,92749854111603,92750229600504)]
theorem point_links_checked11490 : (cuts11490.take 2).map (fun c => (1509949441-1+2*2^9*c.k,92749043797112+c.lower,92749419285365+c.upper)) = pointBounds11490 := by
 decide +kernel
def cuts11491 : List PrefixCut := [⟨10,90775166,90775238⟩,
⟨57,520224730,520225137⟩,
⟨104,942950694,942951433⟩,
⟨128,1157104315,1157105219⟩]
theorem checked11491 : checkPrefixCuts (2^48) 1510080513 9 Manual.Count131072.C011491.packed 128 cuts11491 = true := by
 decide +kernel
def pointBounds11491 : List (Nat × Nat × Nat) := [(1510090752,92750280592366,92750656081604),(1510138880,92750710041930,92751085531503),(1510187008,92751132767894,92751508257799)]
theorem point_links_checked11491 : (cuts11491.take 3).map (fun c => (1510080513-1+2*2^9*c.k,92750189817200+c.lower,92750565306366+c.upper)) = pointBounds11491 := by
 decide +kernel
def cuts11492 : List PrefixCut := [⟨23,210236169,210236337⟩,
⟨70,631630420,631630916⟩,
⟨117,1056925175,1056926008⟩,
⟨128,1156444410,1156445321⟩]
theorem checked11492 : checkPrefixCuts (2^48) 1510211585 9 Manual.Count131072.C011492.packed 128 cuts11492 = true := by
 decide +kernel
def pointBounds11492 : List (Nat × Nat × Nat) := [(1510235136,92751557157684,92751932647922),(1510283264,92751978551935,92752354042501),(1510331392,92752403846690,92752779337593)]
theorem point_links_checked11492 : (cuts11492.take 3).map (fun c => (1510211585-1+2*2^9*c.k,92751346921515+c.lower,92751722411585+c.upper)) = pointBounds11492 := by
 decide +kernel
def cuts11493 : List PrefixCut := [⟨36,321102799,321103054⟩,
⟨83,743015950,743016537⟩,
⟨128,1149821538,1149822445⟩]
theorem checked11493 : checkPrefixCuts (2^48) 1510342657 9 Manual.Count131072.C011493.packed 128 cuts11493 = true := by
 decide +kernel
def pointBounds11493 : List (Nat × Nat × Nat) := [(1510379520,92752824468724,92753199959960),(1510427648,92753246381875,92753621873443)]
theorem point_links_checked11493 : (cuts11493.take 2).map (fun c => (1510342657-1+2*2^9*c.k,92752503365925+c.lower,92752878856906+c.upper)) = pointBounds11493 := by
 decide +kernel
def cuts11494 : List PrefixCut := [⟨2,19007558,19007573⟩,
⟨49,448161254,448161610⟩,
⟨96,866866308,866866998⟩,
⟨128,1156430259,1156431175⟩]
theorem checked11494 : checkPrefixCuts (2^48) 1510473729 9 Manual.Count131072.C011494.packed 128 cuts11494 = true := by
 decide +kernel
def pointBounds11494 : List (Nat × Nat × Nat) := [(1510475776,92753672195021,92754047686924),(1510523904,92754101348717,92754476840961),(1510572032,92754520053771,92754895546349)]
theorem point_links_checked11494 : (cuts11494.take 3).map (fun c => (1510473729-1+2*2^9*c.k,92753653187463+c.lower,92754028679351+c.upper)) = pointBounds11494 := by
 decide +kernel
def cuts11495 : List PrefixCut := [⟨15,136581067,136581172⟩,
⟨62,545756596,545757030⟩,
⟨109,966471147,966471914⟩,
⟨128,1138069659,1138070564⟩]
theorem checked11495 : checkPrefixCuts (2^48) 1510604801 9 Manual.Count131072.C011495.packed 128 cuts11495 = true := by
 decide +kernel
def pointBounds11495 : List (Nat × Nat × Nat) := [(1510620160,92754946198789,92755321691698),(1510668288,92755355374318,92755730867556),(1510716416,92755776088869,92756151582440)]
theorem point_links_checked11495 : (cuts11495.take 3).map (fun c => (1510604801-1+2*2^9*c.k,92754809617722+c.lower,92755185110526+c.upper)) = pointBounds11495 := by
 decide +kernel
def cuts11496 : List PrefixCut := [⟨28,255250994,255251196⟩,
⟨75,671094682,671095210⟩,
⟨122,1081894861,1081895715⟩,
⟨128,1138343941,1138344840⟩]
theorem checked11496 : checkPrefixCuts (2^48) 1510735873 9 Manual.Count131072.C011496.packed 128 cuts11496 = true := by
 decide +kernel
def pointBounds11496 : List (Nat × Nat × Nat) := [(1510764544,92756202938375,92756578432286),(1510812672,92756618782063,92756994276300),(1510860800,92757029582242,92757405076805)]
theorem point_links_checked11496 : (cuts11496.take 3).map (fun c => (1510735873-1+2*2^9*c.k,92755947687381+c.lower,92756323181090+c.upper)) = pointBounds11496 := by
 decide +kernel
def cuts11497 : List PrefixCut := [⟨41,374644550,374644846⟩,
⟨88,793056613,793057238⟩,
⟨128,1155011528,1155012444⟩]
theorem checked11497 : checkPrefixCuts (2^48) 1510866945 9 Manual.Count131072.C011497.packed 128 cuts11497 = true := by
 decide +kernel
def pointBounds11497 : List (Nat × Nat × Nat) := [(1510908928,92757460675872,92757836170776),(1510957056,92757879087935,92758254583168)]
theorem point_links_checked11497 : (cuts11497.take 2).map (fun c => (1510866945-1+2*2^9*c.k,92757086031322+c.lower,92757461525930+c.upper)) = pointBounds11497 := by
 decide +kernel
def cuts11498 : List PrefixCut := [⟨7,64267852,64267902⟩,
⟨54,485261202,485261583⟩,
⟨101,909221465,909222180⟩,
⟨128,1153420923,1153421832⟩]
theorem checked11498 : checkPrefixCuts (2^48) 1510998017 9 Manual.Count131072.C011498.packed 128 cuts11498 = true := by
 decide +kernel
def pointBounds11498 : List (Nat × Nat × Nat) := [(1511005184,92758305310702,92758680806276),(1511053312,92758726304052,92759101799957),(1511101440,92759150264315,92759525760554)]
theorem point_links_checked11498 : (cuts11498.take 3).map (fun c => (1510998017-1+2*2^9*c.k,92758241042850+c.lower,92758616538374+c.upper)) = pointBounds11498 := by
 decide +kernel
def cuts11499 : List PrefixCut := [⟨20,177512119,177512258⟩,
⟨67,594926268,594926736⟩,
⟨114,1017914899,1017915699⟩,
⟨128,1143821694,1143822593⟩]
theorem checked11499 : checkPrefixCuts (2^48) 1511129089 9 Manual.Count131072.C011499.packed 128 cuts11499 = true := by
 decide +kernel
def pointBounds11499 : List (Nat × Nat × Nat) := [(1511149568,92759571975892,92759947472464),(1511197696,92759989390041,92760364886942),(1511245824,92760412378672,92760787875905)]
theorem point_links_checked11499 : (cuts11499.take 3).map (fun c => (1511129089-1+2*2^9*c.k,92759394463773+c.lower,92759769960206+c.upper)) = pointBounds11499 := by
 decide +kernel
def cuts11500 : List PrefixCut := [⟨33,303959506,303959741⟩,
⟨80,739213086,739213664⟩,
⟨127,1163464937,1163465850⟩,
⟨128,1175197784,1175198706⟩]
theorem checked11500 : checkPrefixCuts (2^48) 1511260161 9 Manual.Count131072.C011500.packed 128 cuts11500 = true := by
 decide +kernel
def pointBounds11500 : List (Nat × Nat × Nat) := [(1511293952,92760842244973,92761217742540),(1511342080,92761277498553,92761652996463),(1511390208,92761701750404,92762077248649)]
theorem point_links_checked11500 : (cuts11500.take 3).map (fun c => (1511260161-1+2*2^9*c.k,92760538285467+c.lower,92760913782799+c.upper)) = pointBounds11500 := by
 decide +kernel
def cuts11501 : List PrefixCut := [⟨46,417533718,417534050⟩,
⟨93,846414167,846414834⟩,
⟨128,1162246117,1162247032⟩]
theorem checked11501 : checkPrefixCuts (2^48) 1511391233 9 Manual.Count131072.C011501.packed 128 cuts11501 = true := by
 decide +kernel
def pointBounds11501 : List (Nat × Nat × Nat) := [(1511438336,92762131016969,92762506515555),(1511486464,92762559897418,92762935396339)]
theorem point_links_checked11501 : (cuts11501.take 2).map (fun c => (1511391233-1+2*2^9*c.k,92761713483251+c.lower,92762088981505+c.upper)) = pointBounds11501 := by
 decide +kernel
def cuts11502 : List PrefixCut := [⟨12,109869018,109869106⟩,
⟨59,524755991,524756406⟩,
⟨106,942422915,942423660⟩,
⟨128,1145013634,1145014540⟩]
theorem checked11502 : checkPrefixCuts (2^48) 1511522305 9 Manual.Count131072.C011502.packed 128 cuts11502 = true := by
 decide +kernel
def pointBounds11502 : List (Nat × Nat × Nat) := [(1511534592,92762985598386,92763361097643),(1511582720,92763400485359,92763775984943),(1511630848,92763818152283,92764193652197)]
theorem point_links_checked11502 : (cuts11502.take 3).map (fun c => (1511522305-1+2*2^9*c.k,92762875729368+c.lower,92763251228537+c.upper)) = pointBounds11502 := by
 decide +kernel
def cuts11503 : List PrefixCut := [⟨25,224559335,224559514⟩,
⟨72,646668276,646668787⟩,
⟨119,1063178174,1063179018⟩,
⟨128,1143983646,1143984554⟩]
theorem checked11503 : checkPrefixCuts (2^48) 1511653377 9 Manual.Count131072.C011503.packed 128 cuts11503 = true := by
 decide +kernel
def pointBounds11503 : List (Nat × Nat × Nat) := [(1511678976,92764245302337,92764620802591),(1511727104,92764667411278,92765042911864),(1511775232,92765083921176,92765459422095)]
theorem point_links_checked11503 : (cuts11503.take 3).map (fun c => (1511653377-1+2*2^9*c.k,92764020743002+c.lower,92764396243077+c.upper)) = pointBounds11503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000046
