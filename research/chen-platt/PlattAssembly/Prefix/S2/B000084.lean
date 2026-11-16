import PlattAssemblyKernel
import PlattCertificates.Count131072.C012688
import PlattCertificates.Count131072.C012689
import PlattCertificates.Count131072.C012690
import PlattCertificates.Count131072.C012691
import PlattCertificates.Count131072.C012692
import PlattCertificates.Count131072.C012693
import PlattCertificates.Count131072.C012694
import PlattCertificates.Count131072.C012695
import PlattCertificates.Count131072.C012696
import PlattCertificates.Count131072.C012697
import PlattCertificates.Count131072.C012698
import PlattCertificates.Count131072.C012699
import PlattCertificates.Count131072.C012700
import PlattCertificates.Count131072.C012701
import PlattCertificates.Count131072.C012702
import PlattCertificates.Count131072.C012703
import PlattCertificates.Count131072.C012704
import PlattCertificates.Count131072.C012705
import PlattCertificates.Count131072.C012706
import PlattCertificates.Count131072.C012707
import PlattCertificates.Count131072.C012708
import PlattCertificates.Count131072.C012709
import PlattCertificates.Count131072.C012710
import PlattCertificates.Count131072.C012711
import PlattCertificates.Count131072.C012712
import PlattCertificates.Count131072.C012713
import PlattCertificates.Count131072.C012714
import PlattCertificates.Count131072.C012715
import PlattCertificates.Count131072.C012716
import PlattCertificates.Count131072.C012717
import PlattCertificates.Count131072.C012718
import PlattCertificates.Count131072.C012719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12688 : List PrefixCut := [⟨31,248550471,248550656⟩,
⟨82,665604898,665605387⟩,
⟨128,1037059279,1037060041⟩]
theorem checked12688 : checkPrefixCuts (2^48) 1666973697 9 Manual.Count131072.C012688.packed 128 cuts12688 = true := by
 decide +kernel
def pointBounds12688 : List (Nat × Nat × Nat) := [(1667005440,94063669151591,94064045642000),(1667057664,94064086206018,94064462696731)]
theorem point_links_checked12688 : (cuts12688.take 2).map (fun c => (1666973697-1+2*2^9*c.k,94063420601120+c.lower,94063797091344+c.upper)) = pointBounds12688 := by
 decide +kernel
def cuts12689 : List PrefixCut := [⟨5,43054275,43054308⟩,
⟨56,460251441,460251779⟩,
⟨107,879292659,879293301⟩,
⟨128,1053692336,1053693108⟩]
theorem checked12689 : checkPrefixCuts (2^48) 1667104769 9 Manual.Count131072.C012689.packed 128 cuts12689 = true := by
 decide +kernel
def pointBounds12689 : List (Nat × Nat × Nat) := [(1667109888,94064500714674,94064877205693),(1667162112,94064917911840,94065294403164),(1667214336,94065336953058,94065713444686)]
theorem point_links_checked12689 : (cuts12689.take 3).map (fun c => (1667104769-1+2*2^9*c.k,94064457660399+c.lower,94064834151385+c.upper)) = pointBounds12689 := by
 decide +kernel
def cuts12690 : List PrefixCut := [⟨30,243109020,243109201⟩,
⟨81,663474628,663475120⟩,
⟨128,1040779287,1040780051⟩]
theorem checked12690 : checkPrefixCuts (2^48) 1667235841 9 Manual.Count131072.C012690.packed 128 cuts12690 = true := by
 decide +kernel
def pointBounds12690 : List (Nat × Nat × Nat) := [(1667266560,94065754461755,94066130953694),(1667318784,94066174827363,94066551319613)]
theorem point_links_checked12690 : (cuts12690.take 2).map (fun c => (1667235841-1+2*2^9*c.k,94065511352735+c.lower,94065887844493+c.upper)) = pointBounds12690 := by
 decide +kernel
def cuts12691 : List PrefixCut := [⟨4,31905805,31905829⟩,
⟨55,449206524,449206853⟩,
⟨106,859741866,859742496⟩,
⟨128,1034451774,1034452534⟩]
theorem checked12691 : checkPrefixCuts (2^48) 1667366913 9 Manual.Count131072.C012691.packed 128 cuts12691 = true := by
 decide +kernel
def pointBounds12691 : List (Nat × Nat × Nat) := [(1667371008,94066584037827,94066960530373),(1667423232,94067001338546,94067377831397),(1667475456,94067411873888,94067788367040)]
theorem point_links_checked12691 : (cuts12691.take 3).map (fun c => (1667366913-1+2*2^9*c.k,94066552132022+c.lower,94066928624544+c.upper)) = pointBounds12691 := by
 decide +kernel
def cuts12692 : List PrefixCut := [⟨29,238513289,238513465⟩,
⟨80,658644190,658644674⟩,
⟨128,1036227268,1036228034⟩]
theorem checked12692 : checkPrefixCuts (2^48) 1667497985 9 Manual.Count131072.C012692.packed 128 cuts12692 = true := by
 decide +kernel
def pointBounds12692 : List (Nat × Nat × Nat) := [(1667527680,94067825097085,94068201590543),(1667579904,94068245227986,94068621721752)]
theorem point_links_checked12692 : (cuts12692.take 2).map (fun c => (1667497985-1+2*2^9*c.k,94067586583796+c.lower,94067963077078+c.upper)) = pointBounds12692 := by
 decide +kernel
def cuts12693 : List PrefixCut := [⟨3,24811734,24811753⟩,
⟨54,438840134,438840456⟩,
⟨105,863488699,863489335⟩,
⟨128,1042728156,1042728923⟩]
theorem checked12693 : checkPrefixCuts (2^48) 1667629057 9 Manual.Count131072.C012693.packed 128 cuts12693 = true := by
 decide +kernel
def pointBounds12693 : List (Nat × Nat × Nat) := [(1667632128,94068647622798,94069024116865),(1667684352,94069061651198,94069438145568),(1667736576,94069486299763,94069862794447)]
theorem point_links_checked12693 : (cuts12693.take 3).map (fun c => (1667629057-1+2*2^9*c.k,94068622811064+c.lower,94068999305112+c.upper)) = pointBounds12693 := by
 decide +kernel
def cuts12694 : List PrefixCut := [⟨28,227843200,227843369⟩,
⟨79,639638757,639639230⟩,
⟨128,1041970867,1041971637⟩]
theorem checked12694 : checkPrefixCuts (2^48) 1667760129 9 Manual.Count131072.C012694.packed 128 cuts12694 = true := by
 decide +kernel
def pointBounds12694 : List (Nat × Nat × Nat) := [(1667788800,94069893382420,94070269877404),(1667841024,94070305177977,94070681673265)]
theorem point_links_checked12694 : (cuts12694.take 2).map (fun c => (1667760129-1+2*2^9*c.k,94069665539220+c.lower,94070042034035+c.upper)) = pointBounds12694 := by
 decide +kernel
def cuts12695 : List PrefixCut := [⟨2,16032279,16032291⟩,
⟨53,435564790,435565113⟩,
⟨104,849515445,849516068⟩,
⟨128,1047795436,1047796208⟩]
theorem checked12695 : checkPrefixCuts (2^48) 1667891201 9 Manual.Count131072.C012695.packed 128 cuts12695 = true := by
 decide +kernel
def pointBounds12695 : List (Nat × Nat × Nat) := [(1667893248,94070723542366,94071100037963),(1667945472,94071143074877,94071519570785),(1667997696,94071557025532,94071933521740)]
theorem point_links_checked12695 : (cuts12695.take 3).map (fun c => (1667891201-1+2*2^9*c.k,94070707510087+c.lower,94071084005672+c.upper)) = pointBounds12695 := by
 decide +kernel
def cuts12696 : List PrefixCut := [⟨27,224770034,224770199⟩,
⟨78,638019727,638020197⟩,
⟨128,1042313534,1042314307⟩]
theorem checked12696 : checkPrefixCuts (2^48) 1668022273 9 Manual.Count131072.C012696.packed 128 cuts12696 = true := by
 decide +kernel
def pointBounds12696 : List (Nat × Nat × Nat) := [(1668049920,94071980075557,94072356572079),(1668102144,94072393325250,94072769822077)]
theorem point_links_checked12696 : (cuts12696.take 2).map (fun c => (1668022273-1+2*2^9*c.k,94071755305523+c.lower,94072131801880+c.upper)) = pointBounds12696 := by
 decide +kernel
def cuts12697 : List PrefixCut := [⟨1,7255577,7255583⟩,
⟨52,425372643,425372954⟩,
⟨103,852419055,852419679⟩,
⟨128,1052186404,1052187175⟩]
theorem checked12697 : checkPrefixCuts (2^48) 1668153345 9 Manual.Count131072.C012697.packed 128 cuts12697 = true := by
 decide +kernel
def pointBounds12697 : List (Nat × Nat × Nat) := [(1668154368,94072804874634,94073181371770),(1668206592,94073222991700,94073599489141),(1668258816,94073650038112,94074026535866)]
theorem point_links_checked12697 : (cuts12697.take 3).map (fun c => (1668153345-1+2*2^9*c.k,94072797619057+c.lower,94073174116187+c.upper)) = pointBounds12697 := by
 decide +kernel
def cuts12698 : List PrefixCut := [⟨26,208706427,208706580⟩,
⟨77,616998664,616999121⟩,
⟨128,1033545055,1033545818⟩]
theorem checked12698 : checkPrefixCuts (2^48) 1668284417 9 Manual.Count131072.C012698.packed 128 cuts12698 = true := by
 decide +kernel
def pointBounds12698 : List (Nat × Nat × Nat) := [(1668311040,94074058511888,94074435009942),(1668363264,94074466804125,94074843302483),(1668415488,94074883350516,94075259849180)]
theorem point_links_checked12698 : (cuts12698.take 3).map (fun c => (1668284417-1+2*2^9*c.k,94073849805461+c.lower,94074226303362+c.upper)) = pointBounds12698 := by
 decide +kernel
def cuts12699 : List PrefixCut := [⟨51,413159164,413159466⟩,
⟨102,824787165,824787772⟩,
⟨128,1032789347,1032790107⟩]
theorem checked12699 : checkPrefixCuts (2^48) 1668415489 9 Manual.Count131072.C012699.packed 128 cuts12699 = true := by
 decide +kernel
def pointBounds12699 : List (Nat × Nat × Nat) := [(1668467712,94075296509680,94075673008646),(1668519936,94075708137681,94076084636952)]
theorem point_links_checked12699 : (cuts12699.take 2).map (fun c => (1668415489-1+2*2^9*c.k,94074883350516+c.lower,94075259849180+c.upper)) = pointBounds12699 := by
 decide +kernel
def cuts12700 : List PrefixCut := [⟨25,202769420,202769568⟩,
⟨76,615721183,615721635⟩,
⟨127,1030852896,1030853655⟩,
⟨128,1039793013,1039793778⟩]
theorem checked12700 : checkPrefixCuts (2^48) 1668546561 9 Manual.Count131072.C012700.packed 128 cuts12700 = true := by
 decide +kernel
def pointBounds12700 : List (Nat × Nat × Nat) := [(1668572160,94076118909283,94076495408855),(1668624384,94076531861046,94076908360922),(1668676608,94076946992759,94077323492942)]
theorem point_links_checked12700 : (cuts12700.take 3).map (fun c => (1668546561-1+2*2^9*c.k,94075916139863+c.lower,94076292639287+c.upper)) = pointBounds12700 := by
 decide +kernel
def cuts12701 : List PrefixCut := [⟨50,418492118,418492420⟩,
⟨101,823983503,823984110⟩,
⟨128,1038531117,1038531884⟩]
theorem checked12701 : checkPrefixCuts (2^48) 1668677633 9 Manual.Count131072.C012701.packed 128 cuts12701 = true := by
 decide +kernel
def pointBounds12701 : List (Nat × Nat × Nat) := [(1668728832,94077374424994,94077750925485),(1668781056,94077779916379,94078156417175)]
theorem point_links_checked12701 : (cuts12701.take 2).map (fun c => (1668677633-1+2*2^9*c.k,94076955932876+c.lower,94077332433065+c.upper)) = pointBounds12701 := by
 decide +kernel
def cuts12702 : List PrefixCut := [⟨24,188569592,188569733⟩,
⟨75,599770106,599770548⟩,
⟨126,1005729267,1005730009⟩,
⟨128,1021414183,1021414936⟩]
theorem checked12702 : checkPrefixCuts (2^48) 1668808705 9 Manual.Count131072.C012702.packed 128 cuts12702 = true := by
 decide +kernel
def pointBounds12702 : List (Nat × Nat × Nat) := [(1668833280,94078183033585,94078559534682),(1668885504,94078594234099,94078970735497),(1668937728,94079000193260,94079376694958)]
theorem point_links_checked12702 : (cuts12702.take 3).map (fun c => (1668808705-1+2*2^9*c.k,94077994463993+c.lower,94078370964949+c.upper)) = pointBounds12702 := by
 decide +kernel
def cuts12703 : List PrefixCut := [⟨49,406114926,406115230⟩,
⟨100,819131846,819132452⟩,
⟨128,1049161047,1049161822⟩]
theorem checked12703 : checkPrefixCuts (2^48) 1668939777 9 Manual.Count131072.C012703.packed 128 cuts12703 = true := by
 decide +kernel
def pointBounds12703 : List (Nat × Nat × Nat) := [(1668989952,94079421993102,94079798495115),(1669042176,94079835010022,94080211512337)]
theorem point_links_checked12703 : (cuts12703.take 2).map (fun c => (1668939777-1+2*2^9*c.k,94079015878176+c.lower,94079392379885+c.upper)) = pointBounds12703 := by
 decide +kernel
def cuts12704 : List PrefixCut := [⟨23,189551891,189552031⟩,
⟨74,601193997,601194440⟩,
⟨125,1016027143,1016027887⟩,
⟨128,1038454741,1038455501⟩]
theorem checked12704 : checkPrefixCuts (2^48) 1669070849 9 Manual.Count131072.C012704.packed 128 cuts12704 = true := by
 decide +kernel
def pointBounds12704 : List (Nat × Nat × Nat) := [(1669094400,94080254591114,94080631093738),(1669146624,94080666233220,94081042736147),(1669198848,94081081066366,94081457569594)]
theorem point_links_checked12704 : (cuts12704.take 3).map (fun c => (1669070849-1+2*2^9*c.k,94080065039223+c.lower,94080441541707+c.upper)) = pointBounds12704 := by
 decide +kernel
def cuts12705 : List PrefixCut := [⟨48,386827923,386828207⟩,
⟨99,817316862,817317467⟩,
⟨128,1057089757,1057090537⟩]
theorem checked12705 : checkPrefixCuts (2^48) 1669201921 9 Manual.Count131072.C012705.packed 128 cuts12705 = true := by
 decide +kernel
def pointBounds12705 : List (Nat × Nat × Nat) := [(1669251072,94081490321887,94081866825415),(1669303296,94081920810826,94082297314675)]
theorem point_links_checked12705 : (cuts12705.take 2).map (fun c => (1669201921-1+2*2^9*c.k,94081103493964+c.lower,94081479997208+c.upper)) = pointBounds12705 := by
 decide +kernel
def cuts12706 : List PrefixCut := [⟨22,184632372,184632509⟩,
⟨73,589971343,589971783⟩,
⟨124,1005245432,1005246169⟩,
⟨128,1038965862,1038966624⟩]
theorem checked12706 : checkPrefixCuts (2^48) 1669332993 9 Manual.Count131072.C012706.packed 128 cuts12706 = true := by
 decide +kernel
def pointBounds12706 : List (Nat × Nat × Nat) := [(1669355520,94082345216093,94082721720254),(1669407744,94082750555064,94083127059528),(1669459968,94083165829153,94083542333914)]
theorem point_links_checked12706 : (cuts12706.take 3).map (fun c => (1669332993-1+2*2^9*c.k,94082160583721+c.lower,94082537087745+c.upper)) = pointBounds12706 := by
 decide +kernel
def cuts12707 : List PrefixCut := [⟨47,388790507,388790795⟩,
⟨98,802352654,802353249⟩,
⟨128,1048831588,1048832366⟩]
theorem checked12707 : checkPrefixCuts (2^48) 1669464065 9 Manual.Count131072.C012707.packed 128 cuts12707 = true := by
 decide +kernel
def pointBounds12707 : List (Nat × Nat × Nat) := [(1669512192,94083588340090,94083964845164),(1669564416,94084001902237,94084378407618)]
theorem point_links_checked12707 : (cuts12707.take 2).map (fun c => (1669464065-1+2*2^9*c.k,94083199549583+c.lower,94083576054369+c.upper)) = pointBounds12707 := by
 decide +kernel
def cuts12708 : List PrefixCut := [⟨21,170947838,170947965⟩,
⟨72,589710209,589710642⟩,
⟨123,1001716420,1001717152⟩,
⟨128,1043354623,1043355385⟩]
theorem checked12708 : checkPrefixCuts (2^48) 1669595137 9 Manual.Count131072.C012708.packed 128 cuts12708 = true := by
 decide +kernel
def pointBounds12708 : List (Nat × Nat × Nat) := [(1669616640,94084419329009,94084795834700),(1669668864,94084838091380,94085214597377),(1669721088,94085250097591,94085626603887)]
theorem point_links_checked12708 : (cuts12708.take 3).map (fun c => (1669595137-1+2*2^9*c.k,94084248381171+c.lower,94084624886735+c.upper)) = pointBounds12708 := by
 decide +kernel
def cuts12709 : List PrefixCut := [⟨46,370692288,370692568⟩,
⟨97,783178397,783178975⟩,
⟨128,1039058287,1039059052⟩]
theorem checked12709 : checkPrefixCuts (2^48) 1669726209 9 Manual.Count131072.C012709.packed 128 cuts12709 = true := by
 decide +kernel
def pointBounds12709 : List (Nat × Nat × Nat) := [(1669773312,94085662428082,94086038934688),(1669825536,94086074914191,94086451421095)]
theorem point_links_checked12709 : (cuts12709.take 2).map (fun c => (1669726209-1+2*2^9*c.k,94085291735794+c.lower,94085668242120+c.upper)) = pointBounds12709 := by
 decide +kernel
def cuts12710 : List PrefixCut := [⟨20,162492997,162493112⟩,
⟨71,574110523,574110940⟩,
⟨122,968522939,968523647⟩,
⟨128,1017065145,1017065888⟩]
theorem checked12710 : checkPrefixCuts (2^48) 1669857281 9 Manual.Count131072.C012710.packed 128 cuts12710 = true := by
 decide +kernel
def pointBounds12710 : List (Nat × Nat × Nat) := [(1669877760,94086493287078,94086869794284),(1669929984,94086904904604,94087281412112),(1669982208,94087299317020,94087675824819)]
theorem point_links_checked12710 : (cuts12710.take 3).map (fun c => (1669857281-1+2*2^9*c.k,94086330794081+c.lower,94086707301172+c.upper)) = pointBounds12710 := by
 decide +kernel
def cuts12711 : List PrefixCut := [⟨45,371982539,371982810⟩,
⟨96,791651429,791652005⟩,
⟨128,1060805692,1060806464⟩]
theorem checked12711 : checkPrefixCuts (2^48) 1669988353 9 Manual.Count131072.C012711.packed 128 cuts12711 = true := by
 decide +kernel
def pointBounds12711 : List (Nat × Nat × Nat) := [(1670034432,94087719841765,94088096349870),(1670086656,94088139510655,94088516019065)]
theorem point_links_checked12711 : (cuts12711.take 2).map (fun c => (1669988353-1+2*2^9*c.k,94087347859226+c.lower,94087724367060+c.upper)) = pointBounds12711 := by
 decide +kernel
def cuts12712 : List PrefixCut := [⟨19,148479144,148479255⟩,
⟨70,564582726,564583146⟩,
⟨121,979156534,979157261⟩,
⟨128,1037128417,1037129188⟩]
theorem checked12712 : checkPrefixCuts (2^48) 1670119425 9 Manual.Count131072.C012712.packed 128 cuts12712 = true := by
 decide +kernel
def pointBounds12712 : List (Nat × Nat × Nat) := [(1670138880,94088557144062,94088933652779),(1670191104,94088973247644,94089349756670),(1670243328,94089387821452,94089764330785)]
theorem point_links_checked12712 : (cuts12712.take 3).map (fun c => (1670119425-1+2*2^9*c.k,94088408664918+c.lower,94088785173524+c.upper)) = pointBounds12712 := by
 decide +kernel
def cuts12713 : List PrefixCut := [⟨44,348331426,348331683⟩,
⟨95,763890407,763890971⟩,
⟨128,1033002508,1033003272⟩]
theorem checked12713 : checkPrefixCuts (2^48) 1670250497 9 Manual.Count131072.C012713.packed 128 cuts12713 = true := by
 decide +kernel
def pointBounds12713 : List (Nat × Nat × Nat) := [(1670295552,94089794124761,94090170634395),(1670347776,94090209683742,94090586193683)]
theorem point_links_checked12713 : (cuts12713.take 2).map (fun c => (1670250497-1+2*2^9*c.k,94089445793335+c.lower,94089822302712+c.upper)) = pointBounds12713 := by
 decide +kernel
def cuts12714 : List PrefixCut := [⟨18,145085748,145085854⟩,
⟨69,563146215,563146631⟩,
⟨120,983215638,983216367⟩,
⟨128,1051119738,1051120516⟩]
theorem checked12714 : checkPrefixCuts (2^48) 1670381569 9 Manual.Count131072.C012714.packed 128 cuts12714 = true := by
 decide +kernel
def pointBounds12714 : List (Nat × Nat × Nat) := [(1670400000,94090623881591,94091000391838),(1670452224,94091041942058,94091418452615),(1670504448,94091462011481,94091838522351)]
theorem point_links_checked12714 : (cuts12714.take 3).map (fun c => (1670381569-1+2*2^9*c.k,94090478795843+c.lower,94090855305984+c.upper)) = pointBounds12714 := by
 decide +kernel
def cuts12715 : List PrefixCut := [⟨43,341874081,341874339⟩,
⟨94,748269661,748270218⟩,
⟨128,1026943259,1026944019⟩]
theorem checked12715 : checkPrefixCuts (2^48) 1670512641 9 Manual.Count131072.C012715.packed 128 cuts12715 = true := by
 decide +kernel
def pointBounds12715 : List (Nat × Nat × Nat) := [(1670556672,94091871789662,94092248300839),(1670608896,94092278185242,94092654696718)]
theorem point_links_checked12715 : (cuts12715.take 2).map (fun c => (1670512641-1+2*2^9*c.k,94091529915581+c.lower,94091906426500+c.upper)) = pointBounds12715 := by
 decide +kernel
def cuts12716 : List PrefixCut := [⟨17,136807390,136807490⟩,
⟨68,552275307,552275713⟩,
⟨119,970931288,970932003⟩,
⟨128,1043204972,1043205741⟩]
theorem checked12716 : checkPrefixCuts (2^48) 1670643713 9 Manual.Count131072.C012716.packed 128 cuts12716 = true := by
 decide +kernel
def pointBounds12716 : List (Nat × Nat × Nat) := [(1670661120,94092693666230,94093070178009),(1670713344,94093109134147,94093485646232),(1670765568,94093527790128,94093904302522)]
theorem point_links_checked12716 : (cuts12716.take 3).map (fun c => (1670643713-1+2*2^9*c.k,94092556858840+c.lower,94092933370519+c.upper)) = pointBounds12716 := by
 decide +kernel
def cuts12717 : List PrefixCut := [⟨42,341989024,341989277⟩,
⟨93,750847996,750848549⟩,
⟨128,1032173364,1032174123⟩]
theorem checked12717 : checkPrefixCuts (2^48) 1670774785 9 Manual.Count131072.C012717.packed 128 cuts12717 = true := by
 decide +kernel
def pointBounds12717 : List (Nat × Nat × Nat) := [(1670817792,94093942052836,94094318565537),(1670870016,94094350911808,94094727424809)]
theorem point_links_checked12717 : (cuts12717.take 2).map (fun c => (1670774785-1+2*2^9*c.k,94093600063812+c.lower,94093976576260+c.upper)) = pointBounds12717 := by
 decide +kernel
def cuts12718 : List PrefixCut := [⟨16,129037030,129037126⟩,
⟨67,536185898,536186295⟩,
⟨118,957303243,957303948⟩,
⟨128,1039335348,1039336113⟩]
theorem checked12718 : checkPrefixCuts (2^48) 1670905857 9 Manual.Count131072.C012718.packed 128 cuts12718 = true := by
 decide +kernel
def pointBounds12718 : List (Nat × Nat × Nat) := [(1670922240,94094761274206,94095137787509),(1670974464,94095168423074,94095544936678),(1671026688,94095589540419,94095966054331)]
theorem point_links_checked12718 : (cuts12718.take 3).map (fun c => (1670905857-1+2*2^9*c.k,94094632237176+c.lower,94095008750383+c.upper)) = pointBounds12718 := by
 decide +kernel
def cuts12719 : List PrefixCut := [⟨41,338566693,338566938⟩,
⟨92,751741216,751741765⟩,
⟨128,1041107162,1041107928⟩]
theorem checked12719 : checkPrefixCuts (2^48) 1671036929 9 Manual.Count131072.C012719.packed 128 cuts12719 = true := by
 decide +kernel
def pointBounds12719 : List (Nat × Nat × Nat) := [(1671078912,94096010139217,94096386653434),(1671131136,94096423313740,94096799828261)]
theorem point_links_checked12719 : (cuts12719.take 2).map (fun c => (1671036929-1+2*2^9*c.k,94095671572524+c.lower,94096048086496+c.upper)) = pointBounds12719 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000084
