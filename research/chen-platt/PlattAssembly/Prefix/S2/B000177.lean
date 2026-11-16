import PlattAssemblyKernel
import PlattCertificates.Count131072.C015664
import PlattCertificates.Count131072.C015665
import PlattCertificates.Count131072.C015666
import PlattCertificates.Count131072.C015667
import PlattCertificates.Count131072.C015668
import PlattCertificates.Count131072.C015669
import PlattCertificates.Count131072.C015670
import PlattCertificates.Count131072.C015671
import PlattCertificates.Count131072.C015672
import PlattCertificates.Count131072.C015673
import PlattCertificates.Count131072.C015674
import PlattCertificates.Count131072.C015675
import PlattCertificates.Count131072.C015676
import PlattCertificates.Count131072.C015677
import PlattCertificates.Count131072.C015678
import PlattCertificates.Count131072.C015679
import PlattCertificates.Count131072.C015680
import PlattCertificates.Count131072.C015681
import PlattCertificates.Count131072.C015682
import PlattCertificates.Count131072.C015683
import PlattCertificates.Count131072.C015684
import PlattCertificates.Count131072.C015685
import PlattCertificates.Count131072.C015686
import PlattCertificates.Count131072.C015687
import PlattCertificates.Count131072.C015688
import PlattCertificates.Count131072.C015689
import PlattCertificates.Count131072.C015690
import PlattCertificates.Count131072.C015691
import PlattCertificates.Count131072.C015692
import PlattCertificates.Count131072.C015693
import PlattCertificates.Count131072.C015694
import PlattCertificates.Count131072.C015695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000177
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15664 : List PrefixCut := [⟨24,155169564,155169662⟩,
⟨87,564704400,564704759⟩,
⟨128,834117381,834117912⟩]
theorem checked15664 : checkPrefixCuts (2^48) 2057043969 9 Manual.Count131072.C015664.packed 128 cuts15664 = true := by
 decide +kernel
def pointBounds15664 : List (Nat × Nat × Nat) := [(2057068544,96837020260258,96837398668414),(2057133056,96837429795094,96837808203511)]
theorem point_links_checked15664 : (cuts15664.take 2).map (fun c => (2057043969-1+2*2^9*c.k,96836865090694+c.lower,96837243498752+c.upper)) = pointBounds15664 := by
 decide +kernel
def cuts15665 : List PrefixCut := [⟨22,140382625,140382720⟩,
⟨85,547565778,547566139⟩,
⟨128,826812690,826813233⟩]
theorem checked15665 : checkPrefixCuts (2^48) 2057175041 9 Manual.Count131072.C015665.packed 128 cuts15665 = true := by
 decide +kernel
def pointBounds15665 : List (Nat × Nat × Nat) := [(2057197568,96837839590700,96838217999384),(2057262080,96838246773853,96838625182803)]
theorem point_links_checked15665 : (cuts15665.take 2).map (fun c => (2057175041-1+2*2^9*c.k,96837699208075+c.lower,96838077616664+c.upper)) = pointBounds15665 := by
 decide +kernel
def cuts15666 : List PrefixCut := [⟨20,128060286,128060370⟩,
⟨83,539869592,539869945⟩,
⟨128,841809333,841809879⟩]
theorem checked15666 : checkPrefixCuts (2^48) 2057306113 9 Manual.Count131072.C015666.packed 128 cuts15666 = true := by
 decide +kernel
def pointBounds15666 : List (Nat × Nat × Nat) := [(2057326592,96838654081051,96839032490267),(2057391104,96839065890357,96839444299842)]
theorem point_links_checked15666 : (cuts15666.take 2).map (fun c => (2057306113-1+2*2^9*c.k,96838526020765+c.lower,96838904429897+c.upper)) = pointBounds15666 := by
 decide +kernel
def cuts15667 : List PrefixCut := [⟨18,120117324,120117403⟩,
⟨81,529711856,529712199⟩,
⟨128,828486024,828486561⟩]
theorem checked15667 : checkPrefixCuts (2^48) 2057437185 9 Manual.Count131072.C015667.packed 128 cuts15667 = true := by
 decide +kernel
def pointBounds15667 : List (Nat × Nat × Nat) := [(2057455616,96839487947422,96839866357179),(2057520128,96839897541954,96840275951975)]
theorem point_links_checked15667 : (cuts15667.take 2).map (fun c => (2057437185-1+2*2^9*c.k,96839367830098+c.lower,96839746239776+c.upper)) = pointBounds15667 := by
 decide +kernel
def cuts15668 : List PrefixCut := [⟨16,105472205,105472274⟩,
⟨79,514493886,514494223⟩,
⟨128,821183172,821183709⟩]
theorem checked15668 : checkPrefixCuts (2^48) 2057568257 9 Manual.Count131072.C015668.packed 128 cuts15668 = true := by
 decide +kernel
def pointBounds15668 : List (Nat × Nat × Nat) := [(2057584640,96840301788327,96840680198611),(2057649152,96840710810008,96841089220560)]
theorem point_links_checked15668 : (cuts15668.take 2).map (fun c => (2057568257-1+2*2^9*c.k,96840196316122+c.lower,96840574726337+c.upper)) = pointBounds15668 := by
 decide +kernel
def cuts15669 : List PrefixCut := [⟨14,95890198,95890258⟩,
⟨77,497362957,497363277⟩,
⟨128,835630017,835630553⟩]
theorem checked15669 : checkPrefixCuts (2^48) 2057699329 9 Manual.Count131072.C015669.packed 128 cuts15669 = true := by
 decide +kernel
def pointBounds15669 : List (Nat × Nat × Nat) := [(2057713664,96841113389492,96841491800304),(2057778176,96841514862251,96841893273323)]
theorem point_links_checked15669 : (cuts15669.take 2).map (fun c => (2057699329-1+2*2^9*c.k,96841017499294+c.lower,96841395910046+c.upper)) = pointBounds15669 := by
 decide +kernel
def cuts15670 : List PrefixCut := [⟨12,73041565,73041615⟩,
⟨75,485841736,485842053⟩,
⟨128,829968727,829969265⟩]
theorem checked15670 : checkPrefixCuts (2^48) 2057830401 9 Manual.Count131072.C015670.packed 128 cuts15670 = true := by
 decide +kernel
def pointBounds15670 : List (Nat × Nat × Nat) := [(2057842688,96841926170876,96842304582214),(2057907200,96842338971047,96842717382652)]
theorem point_links_checked15670 : (cuts15670.take 2).map (fun c => (2057830401-1+2*2^9*c.k,96841853129311+c.lower,96842231540599+c.upper)) = pointBounds15670 := by
 decide +kernel
def cuts15671 : List PrefixCut := [⟨10,64693770,64693813⟩,
⟨73,476647413,476647728⟩,
⟨128,833882274,833882819⟩]
theorem checked15671 : checkPrefixCuts (2^48) 2057961473 9 Manual.Count131072.C015671.packed 128 cuts15671 = true := by
 decide +kernel
def pointBounds15671 : List (Nat × Nat × Nat) := [(2057971712,96842747791808,96843126203677),(2058036224,96843159745451,96843538157592)]
theorem point_links_checked15671 : (cuts15671.take 2).map (fun c => (2057961473-1+2*2^9*c.k,96842683098038+c.lower,96843061509864+c.upper)) = pointBounds15671 := by
 decide +kernel
def cuts15672 : List PrefixCut := [⟨8,50192629,50192661⟩,
⟨71,449264798,449265090⟩,
⟨128,821247049,821247581⟩]
theorem checked15672 : checkPrefixCuts (2^48) 2058092545 9 Manual.Count131072.C015672.packed 128 cuts15672 = true := by
 decide +kernel
def pointBounds15672 : List (Nat × Nat × Nat) := [(2058100736,96843567172941,96843945585344),(2058165248,96843966245110,96844344657773)]
theorem point_links_checked15672 : (cuts15672.take 2).map (fun c => (2058092545-1+2*2^9*c.k,96843516980312+c.lower,96843895392683+c.upper)) = pointBounds15672 := by
 decide +kernel
def cuts15673 : List PrefixCut := [⟨6,44172195,44172223⟩,
⟨69,454570019,454570316⟩,
⟨128,848135104,848135653⟩]
theorem checked15673 : checkPrefixCuts (2^48) 2058223617 9 Manual.Count131072.C015673.packed 128 cuts15673 = true := by
 decide +kernel
def pointBounds15673 : List (Nat × Nat × Nat) := [(2058229760,96844382399556,96844760812487),(2058294272,96844792797380,96845171210580)]
theorem point_links_checked15673 : (cuts15673.take 2).map (fun c => (2058223617-1+2*2^9*c.k,96844338227361+c.lower,96844716640264+c.upper)) = pointBounds15673 := by
 decide +kernel
def cuts15674 : List PrefixCut := [⟨4,26255497,26255514⟩,
⟨67,440730000,440730282⟩,
⟨128,835774469,835775010⟩]
theorem checked15674 : checkPrefixCuts (2^48) 2058354689 9 Manual.Count131072.C015674.packed 128 cuts15674 = true := by
 decide +kernel
def pointBounds15674 : List (Nat × Nat × Nat) := [(2058358784,96845212617962,96845591031431),(2058423296,96845627092465,96846005506199)]
theorem point_links_checked15674 : (cuts15674.take 2).map (fun c => (2058354689-1+2*2^9*c.k,96845186362465+c.lower,96845564775917+c.upper)) = pointBounds15674 := by
 decide +kernel
def cuts15675 : List PrefixCut := [⟨2,13400396,13400405⟩,
⟨65,426071205,426071485⟩,
⟨128,843241269,843241818⟩]
theorem checked15675 : checkPrefixCuts (2^48) 2058485761 9 Manual.Count131072.C015675.packed 128 cuts15675 = true := by
 decide +kernel
def pointBounds15675 : List (Nat × Nat × Nat) := [(2058487808,96846035537330,96846413951332),(2058552320,96846448208139,96846826622412),(2058616832,96846865378203,96847243792745)]
theorem point_links_checked15675 : (cuts15675.take 3).map (fun c => (2058485761-1+2*2^9*c.k,96846022136934+c.lower,96846400550927+c.upper)) = pointBounds15675 := by
 decide +kernel
def cuts15676 : List PrefixCut := [⟨63,406765739,406766013⟩,
⟨126,816663285,816663818⟩,
⟨128,830061988,830062530⟩]
theorem checked15676 : checkPrefixCuts (2^48) 2058616833 9 Manual.Count131072.C015676.packed 128 cuts15676 = true := by
 decide +kernel
def pointBounds15676 : List (Nat × Nat × Nat) := [(2058681344,96847272143942,96847650558758),(2058745856,96847682041488,96848060456563)]
theorem point_links_checked15676 : (cuts15676.take 2).map (fun c => (2058616833-1+2*2^9*c.k,96846865378203+c.lower,96847243792745+c.upper)) = pointBounds15676 := by
 decide +kernel
def cuts15677 : List PrefixCut := [⟨61,397853287,397853535⟩,
⟨124,812783678,812784198⟩,
⟨128,838622403,838622940⟩]
theorem checked15677 : checkPrefixCuts (2^48) 2058747905 9 Manual.Count131072.C015677.packed 128 cuts15677 = true := by
 decide +kernel
def pointBounds15677 : List (Nat × Nat × Nat) := [(2058810368,96848093293478,96848471708810),(2058874880,96848508223869,96848886639473)]
theorem point_links_checked15677 : (cuts15677.take 2).map (fun c => (2058747905-1+2*2^9*c.k,96847695440191+c.lower,96848073855275+c.upper)) = pointBounds15677 := by
 decide +kernel
def cuts15678 : List PrefixCut := [⟨59,382106329,382106586⟩,
⟨122,788124745,788125265⟩,
⟨128,829546116,829546663⟩]
theorem checked15678 : checkPrefixCuts (2^48) 2058878977 9 Manual.Count131072.C015678.packed 128 cuts15678 = true := by
 decide +kernel
def pointBounds15678 : List (Nat × Nat × Nat) := [(2058939392,96848916168923,96849294584801),(2059003904,96849322187339,96849700603480)]
theorem point_links_checked15678 : (cuts15678.take 2).map (fun c => (2058878977-1+2*2^9*c.k,96848534062594+c.lower,96848912478215+c.upper)) = pointBounds15678 := by
 decide +kernel
def cuts15679 : List PrefixCut := [⟨57,367181724,367181962⟩,
⟨120,782060107,782060612⟩,
⟨128,833731024,833731563⟩]
theorem checked15679 : checkPrefixCuts (2^48) 2059010049 9 Manual.Count131072.C015679.packed 128 cuts15679 = true := by
 decide +kernel
def pointBounds15679 : List (Nat × Nat × Nat) := [(2059068416,96849730790434,96850109206840),(2059132928,96850145668817,96850524085490)]
theorem point_links_checked15679 : (cuts15679.take 2).map (fun c => (2059010049-1+2*2^9*c.k,96849363608710+c.lower,96849742024878+c.upper)) = pointBounds15679 := by
 decide +kernel
def cuts15680 : List PrefixCut := [⟨55,361144056,361144288⟩,
⟨118,770392091,770392590⟩,
⟨128,833814823,833815366⟩]
theorem checked15680 : checkPrefixCuts (2^48) 2059141121 9 Manual.Count131072.C015680.packed 128 cuts15680 = true := by
 decide +kernel
def pointBounds15680 : List (Nat × Nat × Nat) := [(2059197440,96850558483790,96850936900729),(2059261952,96850967731825,96851346149031)]
theorem point_links_checked15680 : (cuts15680.take 2).map (fun c => (2059141121-1+2*2^9*c.k,96850197339734+c.lower,96850575756441+c.upper)) = pointBounds15680 := by
 decide +kernel
def cuts15681 : List PrefixCut := [⟨53,348546147,348546373⟩,
⟨116,750387856,750388346⟩,
⟨128,827474412,827474953⟩]
theorem checked15681 : checkPrefixCuts (2^48) 2059272193 9 Manual.Count131072.C015681.packed 128 cuts15681 = true := by
 decide +kernel
def pointBounds15681 : List (Nat × Nat × Nat) := [(2059326464,96851379700704,96851758118180),(2059390976,96851781542413,96852159960153)]
theorem point_links_checked15681 : (cuts15681.take 2).map (fun c => (2059272193-1+2*2^9*c.k,96851031154557+c.lower,96851409571807+c.upper)) = pointBounds15681 := by
 decide +kernel
def cuts15682 : List PrefixCut := [⟨51,335266578,335266797⟩,
⟨114,749383593,749384088⟩,
⟨128,842318954,842319507⟩]
theorem checked15682 : checkPrefixCuts (2^48) 2059403265 9 Manual.Count131072.C015682.packed 128 cuts15682 = true := by
 decide +kernel
def pointBounds15682 : List (Nat × Nat × Nat) := [(2059455488,96852193895547,96852572313557),(2059520000,96852608012562,96852986430848)]
theorem point_links_checked15682 : (cuts15682.take 2).map (fun c => (2059403265-1+2*2^9*c.k,96851858628969+c.lower,96852237046760+c.upper)) = pointBounds15682 := by
 decide +kernel
def cuts15683 : List PrefixCut := [⟨49,317615343,317615548⟩,
⟨112,722959934,722960408⟩,
⟨128,827232300,827232840⟩]
theorem checked15683 : checkPrefixCuts (2^48) 2059534337 9 Manual.Count131072.C015683.packed 128 cuts15683 = true := by
 decide +kernel
def pointBounds15683 : List (Nat × Nat × Nat) := [(2059584512,96853018563266,96853396981815),(2059649024,96853423907857,96853802326675)]
theorem point_links_checked15683 : (cuts15683.take 2).map (fun c => (2059534337-1+2*2^9*c.k,96852700947923+c.lower,96853079366267+c.upper)) = pointBounds15683 := by
 decide +kernel
def cuts15684 : List PrefixCut := [⟨47,298189672,298189866⟩,
⟨110,709385044,709385504⟩,
⟨128,827589365,827589904⟩]
theorem checked15684 : checkPrefixCuts (2^48) 2059665409 9 Manual.Count131072.C015684.packed 128 cuts15684 = true := by
 decide +kernel
def pointBounds15684 : List (Nat × Nat × Nat) := [(2059713536,96853826369895,96854204788973),(2059778048,96854237565267,96854615984611)]
theorem point_links_checked15684 : (cuts15684.take 2).map (fun c => (2059665409-1+2*2^9*c.k,96853528180223+c.lower,96853906599107+c.upper)) = pointBounds15684 := by
 decide +kernel
def cuts15685 : List PrefixCut := [⟨45,297624320,297624509⟩,
⟨108,710843654,710844114⟩,
⟨128,843661408,843661953⟩]
theorem checked15685 : checkPrefixCuts (2^48) 2059796481 9 Manual.Count131072.C015685.packed 128 cuts15685 = true := by
 decide +kernel
def pointBounds15685 : List (Nat × Nat × Nat) := [(2059842560,96854653393908,96855031813520),(2059907072,96855066613242,96855445033125)]
theorem point_links_checked15685 : (cuts15685.take 2).map (fun c => (2059796481-1+2*2^9*c.k,96854355769588+c.lower,96854734189011+c.upper)) = pointBounds15685 := by
 decide +kernel
def cuts15686 : List PrefixCut := [⟨43,272053494,272053671⟩,
⟨106,685383606,685384049⟩,
⟨128,831446572,831447111⟩]
theorem checked15686 : checkPrefixCuts (2^48) 2059927553 9 Manual.Count131072.C015686.packed 128 cuts15686 = true := by
 decide +kernel
def pointBounds15686 : List (Nat × Nat × Nat) := [(2059971584,96855471484490,96855849904635),(2060036096,96855884814602,96856263235013)]
theorem point_links_checked15686 : (cuts15686.take 2).map (fun c => (2059927553-1+2*2^9*c.k,96855199430996+c.lower,96855577850964+c.upper)) = pointBounds15686 := by
 decide +kernel
def cuts15687 : List PrefixCut := [⟨41,271899690,271899865⟩,
⟨104,678372429,678372871⟩,
⟨128,834809812,834810355⟩]
theorem checked15687 : checkPrefixCuts (2^48) 2060058625 9 Manual.Count131072.C015687.packed 128 cuts15687 = true := by
 decide +kernel
def pointBounds15687 : List (Nat × Nat × Nat) := [(2060100608,96856302777258,96856681197940),(2060165120,96856709249997,96857087670946)]
theorem point_links_checked15687 : (cuts15687.take 2).map (fun c => (2060058625-1+2*2^9*c.k,96856030877568+c.lower,96856409298075+c.upper)) = pointBounds15687 := by
 decide +kernel
def cuts15688 : List PrefixCut := [⟨39,253438220,253438386⟩,
⟨102,663984117,663984549⟩,
⟨128,832843838,832844380⟩]
theorem checked15688 : checkPrefixCuts (2^48) 2060189697 9 Manual.Count131072.C015688.packed 128 cuts15688 = true := by
 decide +kernel
def pointBounds15688 : List (Nat × Nat × Nat) := [(2060229632,96857119125600,96857497546816),(2060294144,96857529671497,96857908092979)]
theorem point_links_checked15688 : (cuts15688.take 2).map (fun c => (2060189697-1+2*2^9*c.k,96856865687380+c.lower,96857244108430+c.upper)) = pointBounds15688 := by
 decide +kernel
def cuts15689 : List PrefixCut := [⟨37,244132335,244132497⟩,
⟨100,660253623,660254062⟩,
⟨128,844539574,844540130⟩]
theorem checked15689 : checkPrefixCuts (2^48) 2060320769 9 Manual.Count131072.C015689.packed 128 cuts15689 = true := by
 decide +kernel
def pointBounds15689 : List (Nat × Nat × Nat) := [(2060358656,96857942663553,96858321085307),(2060423168,96858358784841,96858737206872)]
theorem point_links_checked15689 : (cuts15689.take 2).map (fun c => (2060320769-1+2*2^9*c.k,96857698531218+c.lower,96858076952810+c.upper)) = pointBounds15689 := by
 decide +kernel
def cuts15690 : List PrefixCut := [⟨35,233598188,233598343⟩,
⟨98,634393795,634394211⟩,
⟨128,826727558,826728101⟩]
theorem checked15690 : checkPrefixCuts (2^48) 2060451841 9 Manual.Count131072.C015690.packed 128 cuts15690 = true := by
 decide +kernel
def pointBounds15690 : List (Nat × Nat × Nat) := [(2060487680,96858776668980,96859155091283),(2060552192,96859177464587,96859555887151)]
theorem point_links_checked15690 : (cuts15690.take 2).map (fun c => (2060451841-1+2*2^9*c.k,96858543070792+c.lower,96858921492940+c.upper)) = pointBounds15690 := by
 decide +kernel
def cuts15691 : List PrefixCut := [⟨33,208039547,208039683⟩,
⟨96,618371735,618372136⟩,
⟨128,829269830,829270371⟩]
theorem checked15691 : checkPrefixCuts (2^48) 2060582913 9 Manual.Count131072.C015691.packed 128 cuts15691 = true := by
 decide +kernel
def pointBounds15691 : List (Nat × Nat × Nat) := [(2060616704,96859577837897,96859956260724),(2060681216,96859988170085,96860366593177)]
theorem point_links_checked15691 : (cuts15691.take 2).map (fun c => (2060582913-1+2*2^9*c.k,96859369798350+c.lower,96859748221041+c.upper)) = pointBounds15691 := by
 decide +kernel
def cuts15692 : List PrefixCut := [⟨31,203109184,203109314⟩,
⟨94,613688837,613689231⟩,
⟨128,838368576,838369114⟩]
theorem checked15692 : checkPrefixCuts (2^48) 2060713985 9 Manual.Count131072.C015692.packed 128 cuts15692 = true := by
 decide +kernel
def pointBounds15692 : List (Nat × Nat × Nat) := [(2060745728,96860402177364,96860780600726),(2060810240,96860812757017,96861191180643)]
theorem point_links_checked15692 : (cuts15692.take 2).map (fun c => (2060713985-1+2*2^9*c.k,96860199068180+c.lower,96860577491412+c.upper)) = pointBounds15692 := by
 decide +kernel
def cuts15693 : List PrefixCut := [⟨29,185477372,185477491⟩,
⟨92,595348418,595348806⟩,
⟨128,826706128,826706666⟩]
theorem checked15693 : checkPrefixCuts (2^48) 2060845057 9 Manual.Count131072.C015693.packed 128 cuts15693 = true := by
 decide +kernel
def pointBounds15693 : List (Nat × Nat × Nat) := [(2060874752,96861222914128,96861601338017),(2060939264,96861632785174,96862011209332)]
theorem point_links_checked15693 : (cuts15693.take 2).map (fun c => (2060845057-1+2*2^9*c.k,96861037436756+c.lower,96861415860526+c.upper)) = pointBounds15693 := by
 decide +kernel
def cuts15694 : List PrefixCut := [⟨27,177271360,177271476⟩,
⟨90,592169851,592170237⟩,
⟨128,843451637,843452183⟩]
theorem checked15694 : checkPrefixCuts (2^48) 2060976129 9 Manual.Count131072.C015694.packed 128 cuts15694 = true := by
 decide +kernel
def pointBounds15694 : List (Nat × Nat × Nat) := [(2061003776,96862041414244,96862419838668),(2061068288,96862456312735,96862834737429)]
theorem point_links_checked15694 : (cuts15694.take 2).map (fun c => (2060976129-1+2*2^9*c.k,96861864142884+c.lower,96862242567192+c.upper)) = pointBounds15694 := by
 decide +kernel
def cuts15695 : List PrefixCut := [⟨25,164969363,164969471⟩,
⟨88,572057911,572058280⟩,
⟨128,828103327,828103859⟩]
theorem checked15695 : checkPrefixCuts (2^48) 2061107201 9 Manual.Count131072.C015695.packed 128 cuts15695 = true := by
 decide +kernel
def pointBounds15695 : List (Nat × Nat × Nat) := [(2061132800,96862872563884,96863250988846),(2061197312,96863279652432,96863658077655)]
theorem point_links_checked15695 : (cuts15695.take 2).map (fun c => (2061107201-1+2*2^9*c.k,96862707594521+c.lower,96863086019375+c.upper)) = pointBounds15695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000177
