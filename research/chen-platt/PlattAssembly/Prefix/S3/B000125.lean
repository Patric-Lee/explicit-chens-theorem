import PlattAssemblyKernel
import PlattCertificates.Count131072.C024000
import PlattCertificates.Count131072.C024001
import PlattCertificates.Count131072.C024002
import PlattCertificates.Count131072.C024003
import PlattCertificates.Count131072.C024004
import PlattCertificates.Count131072.C024005
import PlattCertificates.Count131072.C024006
import PlattCertificates.Count131072.C024007
import PlattCertificates.Count131072.C024008
import PlattCertificates.Count131072.C024009
import PlattCertificates.Count131072.C024010
import PlattCertificates.Count131072.C024011
import PlattCertificates.Count131072.C024012
import PlattCertificates.Count131072.C024013
import PlattCertificates.Count131072.C024014
import PlattCertificates.Count131072.C024015
import PlattCertificates.Count131072.C024016
import PlattCertificates.Count131072.C024017
import PlattCertificates.Count131072.C024018
import PlattCertificates.Count131072.C024019
import PlattCertificates.Count131072.C024020
import PlattCertificates.Count131072.C024021
import PlattCertificates.Count131072.C024022
import PlattCertificates.Count131072.C024023
import PlattCertificates.Count131072.C024024
import PlattCertificates.Count131072.C024025
import PlattCertificates.Count131072.C024026
import PlattCertificates.Count131072.C024027
import PlattCertificates.Count131072.C024028
import PlattCertificates.Count131072.C024029
import PlattCertificates.Count131072.C024030
import PlattCertificates.Count131072.C024031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24000 : List PrefixCut := [⟨70,290796127,290796290⟩,
⟨128,529576396,529576695⟩]
theorem checked24000 : checkPrefixCuts (2^48) 3149660161 9 Manual.Count131072.C024000.packed 128 cuts24000 = true := by
 decide +kernel
def pointBounds24000 : List (Nat × Nat × Nat) := [(3149731840,102374081915663,102374463637037)]
theorem point_links_checked24000 : (cuts24000.take 1).map (fun c => (3149660161-1+2*2^9*c.k,102373791119536+c.lower,102374172840747+c.upper)) = pointBounds24000 := by
 decide +kernel
def cuts24001 : List PrefixCut := [⟨39,168626949,168627042⟩,
⟨128,543852173,543852470⟩]
theorem checked24001 : checkPrefixCuts (2^48) 3149791233 9 Manual.Count131072.C024001.packed 128 cuts24001 = true := by
 decide +kernel
def pointBounds24001 : List (Nat × Nat × Nat) := [(3149831168,102374489322881,102374871044484)]
theorem point_links_checked24001 : (cuts24001.take 1).map (fun c => (3149791233-1+2*2^9*c.k,102374320695932+c.lower,102374702417442+c.upper)) = pointBounds24001 := by
 decide +kernel
def cuts24002 : List PrefixCut := [⟨8,33241621,33241638⟩,
⟨105,439193501,439193748⟩,
⟨128,532123667,532123970⟩]
theorem checked24002 : checkPrefixCuts (2^48) 3149922305 9 Manual.Count131072.C024002.packed 128 cuts24002 = true := by
 decide +kernel
def pointBounds24002 : List (Nat × Nat × Nat) := [(3149930496,102374897789726,102375279511550),(3150029824,102375303741606,102375685463660)]
theorem point_links_checked24002 : (cuts24002.take 2).map (fun c => (3149922305-1+2*2^9*c.k,102374864548105+c.lower,102375246269912+c.upper)) = pointBounds24002 := by
 decide +kernel
def cuts24003 : List PrefixCut := [⟨74,307022127,307022299⟩,
⟨128,531654712,531655007⟩]
theorem checked24003 : checkPrefixCuts (2^48) 3150053377 9 Manual.Count131072.C024003.packed 128 cuts24003 = true := by
 decide +kernel
def pointBounds24003 : List (Nat × Nat × Nat) := [(3150129152,102375703693899,102376085416181)]
theorem point_links_checked24003 : (cuts24003.take 1).map (fun c => (3150053377-1+2*2^9*c.k,102375396671772+c.lower,102375778393882+c.upper)) = pointBounds24003 := by
 decide +kernel
def cuts24004 : List PrefixCut := [⟨43,182276564,182276663⟩,
⟨128,536100119,536100420⟩]
theorem checked24004 : checkPrefixCuts (2^48) 3150184449 9 Manual.Count131072.C024004.packed 128 cuts24004 = true := by
 decide +kernel
def pointBounds24004 : List (Nat × Nat × Nat) := [(3150228480,102376110603048,102376492325552)]
theorem point_links_checked24004 : (cuts24004.take 1).map (fun c => (3150184449-1+2*2^9*c.k,102375928326484+c.lower,102376310048889+c.upper)) = pointBounds24004 := by
 decide +kernel
def cuts24005 : List PrefixCut := [⟨12,47622478,47622504⟩,
⟨109,443784431,443784677⟩,
⟨128,523301231,523301522⟩]
theorem checked24005 : checkPrefixCuts (2^48) 3150315521 9 Manual.Count131072.C024005.packed 128 cuts24005 = true := by
 decide +kernel
def pointBounds24005 : List (Nat × Nat × Nat) := [(3150327808,102376512049081,102376893771813),(3150427136,102376908211034,102377289933986)]
theorem point_links_checked24005 : (cuts24005.take 2).map (fun c => (3150315521-1+2*2^9*c.k,102376464426603+c.lower,102376846149309+c.upper)) = pointBounds24005 := by
 decide +kernel
def cuts24006 : List PrefixCut := [⟨78,333339923,333340113⟩,
⟨128,542577605,542577909⟩]
theorem checked24006 : checkPrefixCuts (2^48) 3150446593 9 Manual.Count131072.C024006.packed 128 cuts24006 = true := by
 decide +kernel
def pointBounds24006 : List (Nat × Nat × Nat) := [(3150526464,102377321067757,102377702790944)]
theorem point_links_checked24006 : (cuts24006.take 1).map (fun c => (3150446593-1+2*2^9*c.k,102376987727834+c.lower,102377369450831+c.upper)) = pointBounds24006 := by
 decide +kernel
def cuts24007 : List PrefixCut := [⟨47,197441517,197441628⟩,
⟨128,544073670,544073975⟩]
theorem checked24007 : checkPrefixCuts (2^48) 3150577665 9 Manual.Count131072.C024007.packed 128 cuts24007 = true := by
 decide +kernel
def pointBounds24007 : List (Nat × Nat × Nat) := [(3150625792,102377727746956,102378109470368)]
theorem point_links_checked24007 : (cuts24007.take 1).map (fun c => (3150577665-1+2*2^9*c.k,102377530305439+c.lower,102377912028740+c.upper)) = pointBounds24007 := by
 decide +kernel
def cuts24008 : List PrefixCut := [⟨16,66734571,66734608⟩,
⟨113,475800159,475800423⟩,
⟨128,539048284,539048581⟩]
theorem checked24008 : checkPrefixCuts (2^48) 3150708737 9 Manual.Count131072.C024008.packed 128 cuts24008 = true := by
 decide +kernel
def pointBounds24008 : List (Nat × Nat × Nat) := [(3150725120,102378141113680,102378522837323),(3150824448,102378550179268,102378931903138)]
theorem point_links_checked24008 : (cuts24008.take 2).map (fun c => (3150708737-1+2*2^9*c.k,102378074379109+c.lower,102378456102715+c.upper)) = pointBounds24008 := by
 decide +kernel
def cuts24009 : List PrefixCut := [⟨82,350717855,350718048⟩,
⟨128,541348613,541348915⟩]
theorem checked24009 : checkPrefixCuts (2^48) 3150839809 9 Manual.Count131072.C024009.packed 128 cuts24009 = true := by
 decide +kernel
def pointBounds24009 : List (Nat × Nat × Nat) := [(3150923776,102378964145248,102379345869344)]
theorem point_links_checked24009 : (cuts24009.take 1).map (fun c => (3150839809-1+2*2^9*c.k,102378613427393+c.lower,102378995151296+c.upper)) = pointBounds24009 := by
 decide +kernel
def cuts24010 : List PrefixCut := [⟨51,212423979,212424095⟩,
⟨128,537306228,537306530⟩]
theorem checked24010 : checkPrefixCuts (2^48) 3150970881 9 Manual.Count131072.C024010.packed 128 cuts24010 = true := by
 decide +kernel
def pointBounds24010 : List (Nat × Nat × Nat) := [(3151023104,102379367199985,102379748924306)]
theorem point_links_checked24010 : (cuts24010.take 1).map (fun c => (3150970881-1+2*2^9*c.k,102379154776006+c.lower,102379536500211+c.upper)) = pointBounds24010 := by
 decide +kernel
def cuts24011 : List PrefixCut := [⟨20,86556479,86556527⟩,
⟨117,487442019,487442299⟩,
⟨128,534604196,534604505⟩]
theorem checked24011 : checkPrefixCuts (2^48) 3151101953 9 Manual.Count131072.C024011.packed 128 cuts24011 = true := by
 decide +kernel
def pointBounds24011 : List (Nat × Nat × Nat) := [(3151122432,102379778638713,102380160363268),(3151221760,102380179524253,102380561249040)]
theorem point_links_checked24011 : (cuts24011.take 2).map (fun c => (3151101953-1+2*2^9*c.k,102379692082234+c.lower,102380073806741+c.upper)) = pointBounds24011 := by
 decide +kernel
def cuts24012 : List PrefixCut := [⟨86,360945726,360945940⟩,
⟨128,535564454,535564769⟩]
theorem checked24012 : checkPrefixCuts (2^48) 3151233025 9 Manual.Count131072.C024012.packed 128 cuts24012 = true := by
 decide +kernel
def pointBounds24012 : List (Nat × Nat × Nat) := [(3151321088,102380587632156,102380969357186)]
theorem point_links_checked24012 : (cuts24012.take 1).map (fun c => (3151233025-1+2*2^9*c.k,102380226686430+c.lower,102380608411246+c.upper)) = pointBounds24012 := by
 decide +kernel
def cuts24013 : List PrefixCut := [⟨55,233386991,233387119⟩,
⟨128,539204245,539204550⟩]
theorem checked24013 : checkPrefixCuts (2^48) 3151364097 9 Manual.Count131072.C024013.packed 128 cuts24013 = true := by
 decide +kernel
def pointBounds24013 : List (Nat × Nat × Nat) := [(3151420416,102380995637875,102381377363134)]
theorem point_links_checked24013 : (cuts24013.take 1).map (fun c => (3151364097-1+2*2^9*c.k,102380762250884+c.lower,102381143976015+c.upper)) = pointBounds24013 := by
 decide +kernel
def cuts24014 : List PrefixCut := [⟨24,101729063,101729127⟩,
⟨121,507833457,507833753⟩,
⟨128,535341277,535341589⟩]
theorem checked24014 : checkPrefixCuts (2^48) 3151495169 9 Manual.Count131072.C024014.packed 128 cuts24014 = true := by
 decide +kernel
def pointBounds24014 : List (Nat × Nat × Nat) := [(3151519744,102381403184192,102381784909692),(3151619072,102381809288586,102382191014318)]
theorem point_links_checked24014 : (cuts24014.take 2).map (fun c => (3151495169-1+2*2^9*c.k,102381301455129+c.lower,102381683180565+c.upper)) = pointBounds24014 := by
 decide +kernel
def cuts24015 : List PrefixCut := [⟨90,374475531,374475739⟩,
⟨128,534783077,534783376⟩]
theorem checked24015 : checkPrefixCuts (2^48) 3151626241 9 Manual.Count131072.C024015.packed 128 cuts24015 = true := by
 decide +kernel
def pointBounds24015 : List (Nat × Nat × Nat) := [(3151718400,102382211271937,102382592997893)]
theorem point_links_checked24015 : (cuts24015.take 1).map (fun c => (3151626241-1+2*2^9*c.k,102381836796406+c.lower,102382218522154+c.upper)) = pointBounds24015 := by
 decide +kernel
def cuts24016 : List PrefixCut := [⟨59,244878257,244878399⟩,
⟨128,529313342,529313648⟩]
theorem checked24016 : checkPrefixCuts (2^48) 3151757313 9 Manual.Count131072.C024016.packed 128 cuts24016 = true := by
 decide +kernel
def pointBounds24016 : List (Nat × Nat × Nat) := [(3151817728,102382616457740,102382998183929)]
theorem point_links_checked24016 : (cuts24016.take 1).map (fun c => (3151757313-1+2*2^9*c.k,102382371579483+c.lower,102382753305530+c.upper)) = pointBounds24016 := by
 decide +kernel
def cuts24017 : List PrefixCut := [⟨28,121005793,121005860⟩,
⟨125,523844189,523844482⟩,
⟨128,538221473,538221774⟩]
theorem checked24017 : checkPrefixCuts (2^48) 3151888385 9 Manual.Count131072.C024017.packed 128 cuts24017 = true := by
 decide +kernel
def pointBounds24017 : List (Nat × Nat × Nat) := [(3151917056,102383021898618,102383403625038),(3152016384,102383424737014,102383806463660)]
theorem point_links_checked24017 : (cuts24017.take 2).map (fun c => (3151888385-1+2*2^9*c.k,102382900892825+c.lower,102383282619178+c.upper)) = pointBounds24017 := by
 decide +kernel
def cuts24018 : List PrefixCut := [⟨94,389966485,389966709⟩,
⟨128,527751203,527751507⟩]
theorem checked24018 : checkPrefixCuts (2^48) 3152019457 9 Manual.Count131072.C024018.packed 128 cuts24018 = true := by
 decide +kernel
def pointBounds24018 : List (Nat × Nat × Nat) := [(3152115712,102383829080783,102384210807661)]
theorem point_links_checked24018 : (cuts24018.take 1).map (fun c => (3152019457-1+2*2^9*c.k,102383439114298+c.lower,102383820840952+c.upper)) = pointBounds24018 := by
 decide +kernel
def cuts24019 : List PrefixCut := [⟨63,258688312,258688460⟩,
⟨128,533979799,533980100⟩]
theorem checked24019 : checkPrefixCuts (2^48) 3152150529 9 Manual.Count131072.C024019.packed 128 cuts24019 = true := by
 decide +kernel
def pointBounds24019 : List (Nat × Nat × Nat) := [(3152215040,102384225553813,102384607280919)]
theorem point_links_checked24019 : (cuts24019.take 1).map (fun c => (3152150529-1+2*2^9*c.k,102383966865501+c.lower,102384348592459+c.upper)) = pointBounds24019 := by
 decide +kernel
def cuts24020 : List PrefixCut := [⟨32,137866810,137866890⟩,
⟨128,538958042,538958352⟩]
theorem checked24020 : checkPrefixCuts (2^48) 3152281601 9 Manual.Count131072.C024020.packed 128 cuts24020 = true := by
 decide +kernel
def pointBounds24020 : List (Nat × Nat × Nat) := [(3152314368,102384638712110,102385020439449)]
theorem point_links_checked24020 : (cuts24020.take 1).map (fun c => (3152281601-1+2*2^9*c.k,102384500845300+c.lower,102384882572559+c.upper)) = pointBounds24020 := by
 decide +kernel
def cuts24021 : List PrefixCut := [⟨1,3660837,3660839⟩,
⟨98,412150216,412150452⟩,
⟨128,536614124,536614433⟩]
theorem checked24021 : checkPrefixCuts (2^48) 3152412673 9 Manual.Count131072.C024021.packed 128 cuts24021 = true := by
 decide +kernel
def pointBounds24021 : List (Nat × Nat × Nat) := [(3152413696,102385043464179,102385425191750),(3152513024,102385451953558,102385833681363)]
theorem point_links_checked24021 : (cuts24021.take 2).map (fun c => (3152412673-1+2*2^9*c.k,102385039803342+c.lower,102385421530911+c.upper)) = pointBounds24021 := by
 decide +kernel
def cuts24022 : List PrefixCut := [⟨67,279994759,279994917⟩,
⟨128,539805905,539806209⟩]
theorem checked24022 : checkPrefixCuts (2^48) 3152543745 9 Manual.Count131072.C024022.packed 128 cuts24022 = true := by
 decide +kernel
def pointBounds24022 : List (Nat × Nat × Nat) := [(3152612352,102385856412225,102386238140261)]
theorem point_links_checked24022 : (cuts24022.take 1).map (fun c => (3152543745-1+2*2^9*c.k,102385576417466+c.lower,102385958145344+c.upper)) = pointBounds24022 := by
 decide +kernel
def cuts24023 : List PrefixCut := [⟨36,150438112,150438195⟩,
⟨128,538890716,538891022⟩]
theorem checked24023 : checkPrefixCuts (2^48) 3152674817 9 Manual.Count131072.C024023.packed 128 cuts24023 = true := by
 decide +kernel
def pointBounds24023 : List (Nat × Nat × Nat) := [(3152711680,102386266661483,102386648389748)]
theorem point_links_checked24023 : (cuts24023.take 1).map (fun c => (3152674817-1+2*2^9*c.k,102386116223371+c.lower,102386497951553+c.upper)) = pointBounds24023 := by
 decide +kernel
def cuts24024 : List PrefixCut := [⟨5,20712384,20712395⟩,
⟨102,425668440,425668681⟩,
⟨128,530833498,530833799⟩]
theorem checked24024 : checkPrefixCuts (2^48) 3152805889 9 Manual.Count131072.C024024.packed 128 cuts24024 = true := by
 decide +kernel
def pointBounds24024 : List (Nat × Nat × Nat) := [(3152811008,102386675826471,102387057554970),(3152910336,102387080782527,102387462511256)]
theorem point_links_checked24024 : (cuts24024.take 2).map (fun c => (3152805889-1+2*2^9*c.k,102386655114087+c.lower,102387036842575+c.upper)) = pointBounds24024 := by
 decide +kernel
def cuts24025 : List PrefixCut := [⟨71,297992772,297992940⟩,
⟨128,536167772,536168070⟩]
theorem checked24025 : checkPrefixCuts (2^48) 3152936961 9 Manual.Count131072.C024025.packed 128 cuts24025 = true := by
 decide +kernel
def pointBounds24025 : List (Nat × Nat × Nat) := [(3153009664,102387483940357,102387865669314)]
theorem point_links_checked24025 : (cuts24025.take 1).map (fun c => (3152936961-1+2*2^9*c.k,102387185947585+c.lower,102387567676374+c.upper)) = pointBounds24025 := by
 decide +kernel
def cuts24026 : List PrefixCut := [⟨40,163006270,163006360⟩,
⟨128,534895632,534895932⟩]
theorem checked24026 : checkPrefixCuts (2^48) 3153068033 9 Manual.Count131072.C024026.packed 128 cuts24026 = true := by
 decide +kernel
def pointBounds24026 : List (Nat × Nat × Nat) := [(3153108992,102387885121627,102388266850804)]
theorem point_links_checked24026 : (cuts24026.take 1).map (fun c => (3153068033-1+2*2^9*c.k,102387722115357+c.lower,102388103844444+c.upper)) = pointBounds24026 := by
 decide +kernel
def cuts24027 : List PrefixCut := [⟨9,39366443,39366467⟩,
⟨106,442486138,442486389⟩,
⟨128,535676773,535677073⟩]
theorem checked24027 : checkPrefixCuts (2^48) 3153199105 9 Manual.Count131072.C024027.packed 128 cuts24027 = true := by
 decide +kernel
def pointBounds24027 : List (Nat × Nat × Nat) := [(3153208320,102388296377432,102388678106843),(3153307648,102388699497127,102389081226765)]
theorem point_links_checked24027 : (cuts24027.take 2).map (fun c => (3153199105-1+2*2^9*c.k,102388257010989+c.lower,102388638740376+c.upper)) = pointBounds24027 := by
 decide +kernel
def cuts24028 : List PrefixCut := [⟨75,312058770,312058948⟩,
⟨128,539582034,539582339⟩]
theorem checked24028 : checkPrefixCuts (2^48) 3153330177 9 Manual.Count131072.C024028.packed 128 cuts24028 = true := by
 decide +kernel
def pointBounds24028 : List (Nat × Nat × Nat) := [(3153406976,102389104746532,102389486476397)]
theorem point_links_checked24028 : (cuts24028.take 1).map (fun c => (3153330177-1+2*2^9*c.k,102388792687762+c.lower,102389174417449+c.upper)) = pointBounds24028 := by
 decide +kernel
def cuts24029 : List PrefixCut := [⟨44,177445686,177445789⟩,
⟨128,523404049,523404351⟩]
theorem checked24029 : checkPrefixCuts (2^48) 3153461249 9 Manual.Count131072.C024029.packed 128 cuts24029 = true := by
 decide +kernel
def pointBounds24029 : List (Nat × Nat × Nat) := [(3153506304,102389509715482,102389891445577)]
theorem point_links_checked24029 : (cuts24029.take 1).map (fun c => (3153461249-1+2*2^9*c.k,102389332269796+c.lower,102389713999788+c.upper)) = pointBounds24029 := by
 decide +kernel
def cuts24030 : List PrefixCut := [⟨13,57569560,57569592⟩,
⟨110,462066638,462066898⟩,
⟨128,540072776,540073080⟩]
theorem checked24030 : checkPrefixCuts (2^48) 3153592321 9 Manual.Count131072.C024030.packed 128 cuts24030 = true := by
 decide +kernel
def pointBounds24030 : List (Nat × Nat × Nat) := [(3153605632,102389913243405,102390294973731),(3153704960,102390317740483,102390699471037)]
theorem point_links_checked24030 : (cuts24030.take 2).map (fun c => (3153592321-1+2*2^9*c.k,102389855673845+c.lower,102390237404139+c.upper)) = pointBounds24030 := by
 decide +kernel
def cuts24031 : List PrefixCut := [⟨79,324782508,324782685⟩,
⟨128,531660798,531661091⟩]
theorem checked24031 : checkPrefixCuts (2^48) 3153723393 9 Manual.Count131072.C024031.packed 128 cuts24031 = true := by
 decide +kernel
def pointBounds24031 : List (Nat × Nat × Nat) := [(3153804288,102390720529129,102391102259904)]
theorem point_links_checked24031 : (cuts24031.take 1).map (fun c => (3153723393-1+2*2^9*c.k,102390395746621+c.lower,102390777477219+c.upper)) = pointBounds24031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000125
