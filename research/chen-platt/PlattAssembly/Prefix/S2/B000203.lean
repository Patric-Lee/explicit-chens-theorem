import PlattAssemblyKernel
import PlattCertificates.Count131072.C016496
import PlattCertificates.Count131072.C016497
import PlattCertificates.Count131072.C016498
import PlattCertificates.Count131072.C016499
import PlattCertificates.Count131072.C016500
import PlattCertificates.Count131072.C016501
import PlattCertificates.Count131072.C016502
import PlattCertificates.Count131072.C016503
import PlattCertificates.Count131072.C016504
import PlattCertificates.Count131072.C016505
import PlattCertificates.Count131072.C016506
import PlattCertificates.Count131072.C016507
import PlattCertificates.Count131072.C016508
import PlattCertificates.Count131072.C016509
import PlattCertificates.Count131072.C016510
import PlattCertificates.Count131072.C016511
import PlattCertificates.Count131072.C016512
import PlattCertificates.Count131072.C016513
import PlattCertificates.Count131072.C016514
import PlattCertificates.Count131072.C016515
import PlattCertificates.Count131072.C016516
import PlattCertificates.Count131072.C016517
import PlattCertificates.Count131072.C016518
import PlattCertificates.Count131072.C016519
import PlattCertificates.Count131072.C016520
import PlattCertificates.Count131072.C016521
import PlattCertificates.Count131072.C016522
import PlattCertificates.Count131072.C016523
import PlattCertificates.Count131072.C016524
import PlattCertificates.Count131072.C016525
import PlattCertificates.Count131072.C016526
import PlattCertificates.Count131072.C016527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16496 : List PrefixCut := [⟨48,296402862,296403048⟩,
⟨115,708444913,708445363⟩,
⟨128,791735339,791735840⟩]
theorem checked16496 : checkPrefixCuts (2^48) 2166095873 9 Manual.Count131072.C016496.packed 128 cuts16496 = true := by
 decide +kernel
def pointBounds16496 : List (Nat × Nat × Nat) := [(2166145024,97514313674744,97514692517707),(2166213632,97514725716795,97515104560022)]
theorem point_links_checked16496 : (cuts16496.take 2).map (fun c => (2166095873-1+2*2^9*c.k,97514017271882+c.lower,97514396114659+c.upper)) = pointBounds16496 := by
 decide +kernel
def cuts16497 : List PrefixCut := [⟨54,336534772,336534983⟩,
⟨121,754787409,754787886⟩,
⟨128,799613334,799613838⟩]
theorem checked16497 : checkPrefixCuts (2^48) 2166226945 9 Manual.Count131072.C016497.packed 128 cuts16497 = true := by
 decide +kernel
def pointBounds16497 : List (Nat × Nat × Nat) := [(2166282240,97515145541993,97515524385482),(2166350848,97515563794630,97515942638385)]
theorem point_links_checked16497 : (cuts16497.take 2).map (fun c => (2166226945-1+2*2^9*c.k,97514809007221+c.lower,97515187850499+c.upper)) = pointBounds16497 := by
 decide +kernel
def cuts16498 : List PrefixCut := [⟨60,367826554,367826785⟩,
⟨127,779556446,779556938⟩,
⟨128,784363566,784364061⟩]
theorem checked16498 : checkPrefixCuts (2^48) 2166358017 9 Manual.Count131072.C016498.packed 128 cuts16498 = true := by
 decide +kernel
def pointBounds16498 : List (Nat × Nat × Nat) := [(2166419456,97515976447109,97516355291122),(2166488064,97516388177001,97516767021275)]
theorem point_links_checked16498 : (cuts16498.take 2).map (fun c => (2166358017-1+2*2^9*c.k,97515608620555+c.lower,97515987464337+c.upper)) = pointBounds16498 := by
 decide +kernel
def cuts16499 : List PrefixCut := [⟨66,415094783,415095046⟩,
⟨128,797178232,797178736⟩]
theorem checked16499 : checkPrefixCuts (2^48) 2166489089 9 Manual.Count131072.C016499.packed 128 cuts16499 = true := by
 decide +kernel
def pointBounds16499 : List (Nat × Nat × Nat) := [(2166556672,97516808078904,97517186923444)]
theorem point_links_checked16499 : (cuts16499.take 1).map (fun c => (2166489089-1+2*2^9*c.k,97516392984121+c.lower,97516771828398+c.upper)) = pointBounds16499 := by
 decide +kernel
def cuts16500 : List PrefixCut := [⟨5,30529818,30529838⟩,
⟨72,445598432,445598715⟩,
⟨128,791543758,791544260⟩]
theorem checked16500 : checkPrefixCuts (2^48) 2166620161 9 Manual.Count131072.C016500.packed 128 cuts16500 = true := by
 decide +kernel
def pointBounds16500 : List (Nat × Nat × Nat) := [(2166625280,97517220692171,97517599536972),(2166693888,97517635760785,97518014605849)]
theorem point_links_checked16500 : (cuts16500.take 2).map (fun c => (2166620161-1+2*2^9*c.k,97517190162353+c.lower,97517569007134+c.upper)) = pointBounds16500 := by
 decide +kernel
def cuts16501 : List PrefixCut := [⟨11,67161443,67161486⟩,
⟨78,484671898,484672207⟩,
⟨128,796302170,796302677⟩]
theorem checked16501 : checkPrefixCuts (2^48) 2166751233 9 Manual.Count131072.C016501.packed 128 cuts16501 = true := by
 decide +kernel
def pointBounds16501 : List (Nat × Nat × Nat) := [(2166762496,97518048867554,97518427712880),(2166831104,97518466378009,97518845223601)]
theorem point_links_checked16501 : (cuts16501.take 2).map (fun c => (2166751233-1+2*2^9*c.k,97517981706111+c.lower,97518360551394+c.upper)) = pointBounds16501 := by
 decide +kernel
def cuts16502 : List PrefixCut := [⟨17,107815368,107815433⟩,
⟨84,527507631,527507959⟩,
⟨128,793526586,793527085⟩]
theorem checked16502 : checkPrefixCuts (2^48) 2166882305 9 Manual.Count131072.C016502.packed 128 cuts16502 = true := by
 decide +kernel
def pointBounds16502 : List (Nat × Nat × Nat) := [(2166899712,97518885823649,97519264669504),(2166968320,97519305515912,97519684362030)]
theorem point_links_checked16502 : (cuts16502.take 2).map (fun c => (2166882305-1+2*2^9*c.k,97518778008281+c.lower,97519156854071+c.upper)) = pointBounds16502 := by
 decide +kernel
def cuts16503 : List PrefixCut := [⟨23,144827342,144827435⟩,
⟨90,554881248,554881605⟩,
⟨128,790231053,790231559⟩]
theorem checked16503 : checkPrefixCuts (2^48) 2167013377 9 Manual.Count131072.C016503.packed 128 cuts16503 = true := by
 decide +kernel
def pointBounds16503 : List (Nat × Nat × Nat) := [(2167036928,97519716362209,97520095208591),(2167105536,97520126416115,97520505262761)]
theorem point_links_checked16503 : (cuts16503.take 2).map (fun c => (2167013377-1+2*2^9*c.k,97519571534867+c.lower,97519950381156+c.upper)) = pointBounds16503 := by
 decide +kernel
def cuts16504 : List PrefixCut := [⟨29,179366972,179367084⟩,
⟨96,586927376,586927748⟩,
⟨128,785637598,785638096⟩]
theorem checked16504 : checkPrefixCuts (2^48) 2167144449 9 Manual.Count131072.C016504.packed 128 cuts16504 = true := by
 decide +kernel
def pointBounds16504 : List (Nat × Nat × Nat) := [(2167174144,97520541132892,97520919979799),(2167242752,97520948693296,97521327540463)]
theorem point_links_checked16504 : (cuts16504.take 2).map (fun c => (2167144449-1+2*2^9*c.k,97520361765920+c.lower,97520740612715+c.upper)) = pointBounds16504 := by
 decide +kernel
def cuts16505 : List PrefixCut := [⟨35,217668694,217668831⟩,
⟨102,635852569,635852968⟩,
⟨128,791434355,791434855⟩]
theorem checked16505 : checkPrefixCuts (2^48) 2167275521 9 Manual.Count131072.C016505.packed 128 cuts16505 = true := by
 decide +kernel
def pointBounds16505 : List (Nat × Nat × Nat) := [(2167311360,97521365072212,97521743919642),(2167379968,97521783256087,97522162103779)]
theorem point_links_checked16505 : (cuts16505.take 2).map (fun c => (2167275521-1+2*2^9*c.k,97521147403518+c.lower,97521526250811+c.upper)) = pointBounds16505 := by
 decide +kernel
def cuts16506 : List PrefixCut := [⟨41,255056541,255056704⟩,
⟨108,666461159,666461581⟩,
⟨128,789698196,789698696⟩]
theorem checked16506 : checkPrefixCuts (2^48) 2167406593 9 Manual.Count131072.C016506.packed 128 cuts16506 = true := by
 decide +kernel
def pointBounds16506 : List (Nat × Nat × Nat) := [(2167448576,97522193894414,97522572742370),(2167517184,97522605299032,97522984147247)]
theorem point_links_checked16506 : (cuts16506.take 2).map (fun c => (2167406593-1+2*2^9*c.k,97521938837873+c.lower,97522317685666+c.upper)) = pointBounds16506 := by
 decide +kernel
def cuts16507 : List PrefixCut := [⟨47,293348843,293349027⟩,
⟨114,714726188,714726639⟩,
⟨128,801856788,801857294⟩]
theorem checked16507 : checkPrefixCuts (2^48) 2167537665 9 Manual.Count131072.C016507.packed 128 cuts16507 = true := by
 decide +kernel
def pointBounds16507 : List (Nat × Nat × Nat) := [(2167585792,97523021884912,97523400733389),(2167654400,97523443262257,97523822111001)]
theorem point_links_checked16507 : (cuts16507.take 2).map (fun c => (2167537665-1+2*2^9*c.k,97522728536069+c.lower,97523107384362+c.upper)) = pointBounds16507 := by
 decide +kernel
def cuts16508 : List PrefixCut := [⟨53,325793177,325793388⟩,
⟨120,739223198,739223671⟩,
⟨128,788823537,788824041⟩]
theorem checked16508 : checkPrefixCuts (2^48) 2167668737 9 Manual.Count131072.C016508.packed 128 cuts16508 = true := by
 decide +kernel
def pointBounds16508 : List (Nat × Nat × Nat) := [(2167723008,97523856186034,97524235035044),(2167791616,97524269616055,97524648465327)]
theorem point_links_checked16508 : (cuts16508.take 2).map (fun c => (2167668737-1+2*2^9*c.k,97523530392857+c.lower,97523909241656+c.upper)) = pointBounds16508 := by
 decide +kernel
def cuts16509 : List PrefixCut := [⟨59,360310941,360311171⟩,
⟨126,774753485,774753979⟩,
⟨128,787087885,787088386⟩]
theorem checked16509 : checkPrefixCuts (2^48) 2167799809 9 Manual.Count131072.C016509.packed 128 cuts16509 = true := by
 decide +kernel
def pointBounds16509 : List (Nat × Nat × Nat) := [(2167860224,97524679527335,97525058376868),(2167928832,97525093969879,97525472819676)]
theorem point_links_checked16509 : (cuts16509.take 2).map (fun c => (2167799809-1+2*2^9*c.k,97524319216394+c.lower,97524698065697+c.upper)) = pointBounds16509 := by
 decide +kernel
def cuts16510 : List PrefixCut := [⟨65,397421039,397421291⟩,
⟨128,783534982,783535475⟩]
theorem checked16510 : checkPrefixCuts (2^48) 2167930881 9 Manual.Count131072.C016510.packed 128 cuts16510 = true := by
 decide +kernel
def pointBounds16510 : List (Nat × Nat × Nat) := [(2167997440,97525503725318,97525882575374)]
theorem point_links_checked16510 : (cuts16510.take 1).map (fun c => (2167930881-1+2*2^9*c.k,97525106304279+c.lower,97525485154083+c.upper)) = pointBounds16510 := by
 decide +kernel
def cuts16511 : List PrefixCut := [⟨4,23498823,23498839⟩,
⟨71,443095127,443095411⟩,
⟨128,796470026,796470532⟩]
theorem checked16511 : checkPrefixCuts (2^48) 2168061953 9 Manual.Count131072.C016511.packed 128 cuts16511 = true := by
 decide +kernel
def pointBounds16511 : List (Nat × Nat × Nat) := [(2168066048,97525913338084,97526292188397),(2168134656,97526332934388,97526711784969)]
theorem point_links_checked16511 : (cuts16511.take 2).map (fun c => (2168061953-1+2*2^9*c.k,97525889839261+c.lower,97526268689558+c.upper)) = pointBounds16511 := by
 decide +kernel
def cuts16512 : List PrefixCut := [⟨10,62702924,62702964⟩,
⟨77,477339562,477339865⟩,
⟨128,793306209,793306714⟩]
theorem checked16512 : checkPrefixCuts (2^48) 2168193025 9 Manual.Count131072.C016512.packed 128 cuts16512 = true := by
 decide +kernel
def pointBounds16512 : List (Nat × Nat × Nat) := [(2168203264,97526749012211,97527127863054),(2168271872,97527163648849,97527542499955)]
theorem point_links_checked16512 : (cuts16512.take 2).map (fun c => (2168193025-1+2*2^9*c.k,97526686309287+c.lower,97527065160090+c.upper)) = pointBounds16512 := by
 decide +kernel
def cuts16513 : List PrefixCut := [⟨16,97358758,97358821⟩,
⟨83,509373056,509373379⟩,
⟨128,795724453,795724956⟩]
theorem checked16513 : checkPrefixCuts (2^48) 2168324097 9 Manual.Count131072.C016513.packed 128 cuts16513 = true := by
 decide +kernel
def pointBounds16513 : List (Nat × Nat × Nat) := [(2168340480,97527576974254,97527955825625),(2168409088,97527988988552,97528367840183)]
theorem point_links_checked16513 : (cuts16513.take 2).map (fun c => (2168324097-1+2*2^9*c.k,97527479615496+c.lower,97527858466804+c.upper)) = pointBounds16513 := by
 decide +kernel
def cuts16514 : List PrefixCut := [⟨22,131231522,131231604⟩,
⟨89,548801142,548801486⟩,
⟨128,792171816,792172312⟩]
theorem checked16514 : checkPrefixCuts (2^48) 2168455169 9 Manual.Count131072.C016514.packed 128 cuts16514 = true := by
 decide +kernel
def pointBounds16514 : List (Nat × Nat × Nat) := [(2168477696,97528406571471,97528785423364),(2168546304,97528824141091,97529202993246)]
theorem point_links_checked16514 : (cuts16514.take 2).map (fun c => (2168455169-1+2*2^9*c.k,97528275339949+c.lower,97528654191760+c.upper)) = pointBounds16514 := by
 decide +kernel
def cuts16515 : List PrefixCut := [⟨28,174445308,174445419⟩,
⟨95,584200980,584201352⟩,
⟨128,787581362,787581863⟩]
theorem checked16515 : checkPrefixCuts (2^48) 2168586241 9 Manual.Count131072.C016515.packed 128 cuts16515 = true := by
 decide +kernel
def pointBounds16515 : List (Nat × Nat × Nat) := [(2168614912,97529241957073,97529620809491),(2168683520,97529651712745,97530030565424)]
theorem point_links_checked16515 : (cuts16515.take 2).map (fun c => (2168586241-1+2*2^9*c.k,97529067511765+c.lower,97529446364072+c.upper)) = pointBounds16515 := by
 decide +kernel
def cuts16516 : List PrefixCut := [⟨34,207270812,207270942⟩,
⟨101,615702675,615703065⟩,
⟨128,784808127,784808621⟩]
theorem checked16516 : checkPrefixCuts (2^48) 2168717313 9 Manual.Count131072.C016516.packed 128 cuts16516 = true := by
 decide +kernel
def pointBounds16516 : List (Nat × Nat × Nat) := [(2168752128,97530062363939,97530441216877),(2168820736,97530470795802,97530849649000)]
theorem point_links_checked16516 : (cuts16516.take 2).map (fun c => (2168717313-1+2*2^9*c.k,97529855093127+c.lower,97530233945935+c.upper)) = pointBounds16516 := by
 decide +kernel
def cuts16517 : List PrefixCut := [⟨40,253199941,253200102⟩,
⟨107,665369485,665369901⟩,
⟨128,796700384,796700882⟩]
theorem checked16517 : checkPrefixCuts (2^48) 2168848385 9 Manual.Count131072.C016517.packed 128 cuts16517 = true := by
 decide +kernel
def pointBounds16517 : List (Nat × Nat × Nat) := [(2168889344,97530893101195,97531271954658),(2168957952,97531305270739,97531684124457)]
theorem point_links_checked16517 : (cuts16517.take 2).map (fun c => (2168848385-1+2*2^9*c.k,97530639901254+c.lower,97531018754556+c.upper)) = pointBounds16517 := by
 decide +kernel
def cuts16518 : List PrefixCut := [⟨46,277581375,277581553⟩,
⟨113,693617861,693618304⟩,
⟨128,788865802,788866305⟩]
theorem checked16518 : checkPrefixCuts (2^48) 2168979457 9 Manual.Count131072.C016518.packed 128 cuts16518 = true := by
 decide +kernel
def pointBounds16518 : List (Nat × Nat × Nat) := [(2169026560,97531714183013,97532093036991),(2169095168,97532130219499,97532509073742)]
theorem point_links_checked16518 : (cuts16518.take 2).map (fun c => (2168979457-1+2*2^9*c.k,97531436601638+c.lower,97531815455438+c.upper)) = pointBounds16518 := by
 decide +kernel
def cuts16519 : List PrefixCut := [⟨52,319607520,319607723⟩,
⟨119,733930854,733931320⟩,
⟨128,790634901,790635402⟩]
theorem checked16519 : checkPrefixCuts (2^48) 2169110529 9 Manual.Count131072.C016519.packed 128 cuts16519 = true := by
 decide +kernel
def pointBounds16519 : List (Nat × Nat × Nat) := [(2169163776,97532545074960,97532923929466),(2169232384,97532959398294,97533338253063)]
theorem point_links_checked16519 : (cuts16519.take 2).map (fun c => (2169110529-1+2*2^9*c.k,97532225467440+c.lower,97532604321743+c.upper)) = pointBounds16519 := by
 decide +kernel
def cuts16520 : List PrefixCut := [⟨58,359292980,359293208⟩,
⟨125,768659500,768659990⟩,
⟨128,787862430,787862932⟩]
theorem checked16520 : checkPrefixCuts (2^48) 2169241601 9 Manual.Count131072.C016520.packed 128 cuts16520 = true := by
 decide +kernel
def pointBounds16520 : List (Nat × Nat × Nat) := [(2169300992,97533375395321,97533754250353),(2169369600,97533784761841,97534163617135)]
theorem point_links_checked16520 : (cuts16520.take 2).map (fun c => (2169241601-1+2*2^9*c.k,97533016102341+c.lower,97533394957145+c.upper)) = pointBounds16520 := by
 decide +kernel
def cuts16521 : List PrefixCut := [⟨64,398065230,398065487⟩,
⟨128,784701063,784701569⟩]
theorem checked16521 : checkPrefixCuts (2^48) 2169372673 9 Manual.Count131072.C016521.packed 128 cuts16521 = true := by
 decide +kernel
def pointBounds16521 : List (Nat × Nat × Nat) := [(2169438208,97534202030001,97534580885564)]
theorem point_links_checked16521 : (cuts16521.take 1).map (fun c => (2169372673-1+2*2^9*c.k,97533803964771+c.lower,97534182820077+c.upper)) = pointBounds16521 := by
 decide +kernel
def cuts16522 : List PrefixCut := [⟨3,17515104,17515114⟩,
⟨70,430475576,430475847⟩,
⟨128,794383757,794384263⟩]
theorem checked16522 : checkPrefixCuts (2^48) 2169503745 9 Manual.Count131072.C016522.packed 128 cuts16522 = true := by
 decide +kernel
def pointBounds16522 : List (Nat × Nat × Nat) := [(2169506816,97534606180938,97534985036760),(2169575424,97535019141410,97535397997493)]
theorem point_links_checked16522 : (cuts16522.take 2).map (fun c => (2169503745-1+2*2^9*c.k,97534588665834+c.lower,97534967521646+c.upper)) = pointBounds16522 := by
 decide +kernel
def cuts16523 : List PrefixCut := [⟨9,58509800,58509836⟩,
⟨76,478319821,478320122⟩,
⟨128,806270975,806271486⟩]
theorem checked16523 : checkPrefixCuts (2^48) 2169634817 9 Manual.Count131072.C016523.packed 128 cuts16523 = true := by
 decide +kernel
def pointBounds16523 : List (Nat × Nat × Nat) := [(2169644032,97535441559391,97535820415745),(2169712640,97535861369412,97536240226031)]
theorem point_links_checked16523 : (cuts16523.take 2).map (fun c => (2169634817-1+2*2^9*c.k,97535383049591+c.lower,97535761905909+c.upper)) = pointBounds16523 := by
 decide +kernel
def cuts16524 : List PrefixCut := [⟨15,91326729,91326787⟩,
⟨82,494894904,494895222⟩,
⟨128,776126800,776127297⟩]
theorem checked16524 : checkPrefixCuts (2^48) 2169765889 9 Manual.Count131072.C016524.packed 128 cuts16524 = true := by
 decide +kernel
def pointBounds16524 : List (Nat × Nat × Nat) := [(2169781248,97536280647295,97536659504182),(2169849856,97536684215470,97537063072617)]
theorem point_links_checked16524 : (cuts16524.take 2).map (fun c => (2169765889-1+2*2^9*c.k,97536189320566+c.lower,97536568177395+c.upper)) = pointBounds16524 := by
 decide +kernel
def cuts16525 : List PrefixCut := [⟨21,125436775,125436855⟩,
⟨88,544026244,544026586⟩,
⟨128,794109986,794110482⟩]
theorem checked16525 : checkPrefixCuts (2^48) 2169896961 9 Manual.Count131072.C016525.packed 128 cuts16525 = true := by
 decide +kernel
def pointBounds16525 : List (Nat × Nat × Nat) := [(2169918464,97537090884141,97537469741547),(2169987072,97537509473610,97537888331278)]
theorem point_links_checked16525 : (cuts16525.take 2).map (fun c => (2169896961-1+2*2^9*c.k,97536965447366+c.lower,97537344304692+c.upper)) = pointBounds16525 := by
 decide +kernel
def cuts16526 : List PrefixCut := [⟨27,162136780,162136883⟩,
⟨94,576678861,576679222⟩,
⟨128,791467802,791468299⟩]
theorem checked16526 : checkPrefixCuts (2^48) 2170028033 9 Manual.Count131072.C016526.packed 128 cuts16526 = true := by
 decide +kernel
def pointBounds16526 : List (Nat × Nat × Nat) := [(2170055680,97537921694132,97538300552057),(2170124288,97538336236213,97538715094396)]
theorem point_links_checked16526 : (cuts16526.take 2).map (fun c => (2170028033-1+2*2^9*c.k,97537759557352+c.lower,97538138415174+c.upper)) = pointBounds16526 := by
 decide +kernel
def cuts16527 : List PrefixCut := [⟨33,197664939,197665067⟩,
⟨100,616979687,616980082⟩,
⟨128,792717003,792717510⟩]
theorem checked16527 : checkPrefixCuts (2^48) 2170159105 9 Manual.Count131072.C016527.packed 128 cuts16527 = true := by
 decide +kernel
def pointBounds16527 : List (Nat × Nat × Nat) := [(2170192896,97538748690093,97539127548540),(2170261504,97539168004841,97539546863555)]
theorem point_links_checked16527 : (cuts16527.take 2).map (fun c => (2170159105-1+2*2^9*c.k,97538551025154+c.lower,97538929883473+c.upper)) = pointBounds16527 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000203
