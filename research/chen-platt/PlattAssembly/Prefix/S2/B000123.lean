import PlattAssemblyKernel
import PlattCertificates.Count131072.C013936
import PlattCertificates.Count131072.C013937
import PlattCertificates.Count131072.C013938
import PlattCertificates.Count131072.C013939
import PlattCertificates.Count131072.C013940
import PlattCertificates.Count131072.C013941
import PlattCertificates.Count131072.C013942
import PlattCertificates.Count131072.C013943
import PlattCertificates.Count131072.C013944
import PlattCertificates.Count131072.C013945
import PlattCertificates.Count131072.C013946
import PlattCertificates.Count131072.C013947
import PlattCertificates.Count131072.C013948
import PlattCertificates.Count131072.C013949
import PlattCertificates.Count131072.C013950
import PlattCertificates.Count131072.C013951
import PlattCertificates.Count131072.C013952
import PlattCertificates.Count131072.C013953
import PlattCertificates.Count131072.C013954
import PlattCertificates.Count131072.C013955
import PlattCertificates.Count131072.C013956
import PlattCertificates.Count131072.C013957
import PlattCertificates.Count131072.C013958
import PlattCertificates.Count131072.C013959
import PlattCertificates.Count131072.C013960
import PlattCertificates.Count131072.C013961
import PlattCertificates.Count131072.C013962
import PlattCertificates.Count131072.C013963
import PlattCertificates.Count131072.C013964
import PlattCertificates.Count131072.C013965
import PlattCertificates.Count131072.C013966
import PlattCertificates.Count131072.C013967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13936 : List PrefixCut := [⟨51,373336254,373336511⟩,
⟨107,779258101,779258645⟩,
⟨128,938855728,938856382⟩]
theorem checked13936 : checkPrefixCuts (2^48) 1830551553 9 Manual.Count131072.C013936.packed 128 cuts13936 = true := by
 decide +kernel
def pointBounds13936 : List (Nat × Nat × Nat) := [(1830603776,95301926599655,95302303976051),(1830661120,95302332521502,95302709898185)]
theorem point_links_checked13936 : (cuts13936.take 2).map (fun c => (1830551553-1+2*2^9*c.k,95301553263401+c.lower,95301930639540+c.upper)) = pointBounds13936 := by
 decide +kernel
def cuts13937 : List PrefixCut := [⟨35,260149280,260149462⟩,
⟨91,674348138,674348610⟩,
⟨128,943093777,943094443⟩]
theorem checked13937 : checkPrefixCuts (2^48) 1830682625 9 Manual.Count131072.C013937.packed 128 cuts13937 = true := by
 decide +kernel
def pointBounds13937 : List (Nat × Nat × Nat) := [(1830718464,95302752268409,95303129645384),(1830775808,95303166467267,95303543844532)]
theorem point_links_checked13937 : (cuts13937.take 2).map (fun c => (1830682625-1+2*2^9*c.k,95302492119129+c.lower,95302869495922+c.upper)) = pointBounds13937 := by
 decide +kernel
def cuts13938 : List PrefixCut := [⟨19,140674140,140674238⟩,
⟨75,556999424,556999815⟩,
⟨128,950405546,950406205⟩]
theorem checked13938 : checkPrefixCuts (2^48) 1830813697 9 Manual.Count131072.C013938.packed 128 cuts13938 = true := by
 decide +kernel
def pointBounds13938 : List (Nat × Nat × Nat) := [(1830833152,95303575887046,95303953264603),(1830890496,95303992212330,95304369590180)]
theorem point_links_checked13938 : (cuts13938.take 2).map (fun c => (1830813697-1+2*2^9*c.k,95303435212906+c.lower,95303812590365+c.upper)) = pointBounds13938 := by
 decide +kernel
def cuts13939 : List PrefixCut := [⟨3,23213519,23213535⟩,
⟨59,427368031,427368326⟩,
⟨115,835199290,835199870⟩,
⟨128,933119943,933120591⟩]
theorem checked13939 : checkPrefixCuts (2^48) 1830944769 9 Manual.Count131072.C013939.packed 128 cuts13939 = true := by
 decide +kernel
def pointBounds13939 : List (Nat × Nat × Nat) := [(1830947840,95304408831971,95304786210105),(1831005184,95304812986483,95305190364896),(1831062528,95305220817742,95305598196440)]
theorem point_links_checked13939 : (cuts13939.take 3).map (fun c => (1830944769-1+2*2^9*c.k,95304385618452+c.lower,95304762996570+c.upper)) = pointBounds13939 := by
 decide +kernel
def cuts13940 : List PrefixCut := [⟨43,323578948,323579170⟩,
⟨99,742144771,742145287⟩,
⟨128,955188603,955189269⟩]
theorem checked13940 : checkPrefixCuts (2^48) 1831075841 9 Manual.Count131072.C013940.packed 128 cuts13940 = true := by
 decide +kernel
def pointBounds13940 : List (Nat × Nat × Nat) := [(1831119872,95305642317343,95306019696331),(1831177216,95306060883166,95306438262448)]
theorem point_links_checked13940 : (cuts13940.take 2).map (fun c => (1831075841-1+2*2^9*c.k,95305318738395+c.lower,95305696117161+c.upper)) = pointBounds13940 := by
 decide +kernel
def cuts13941 : List PrefixCut := [⟨27,203203117,203203259⟩,
⟨83,609292479,609292902⟩,
⟨128,935445962,935446616⟩]
theorem checked13941 : checkPrefixCuts (2^48) 1831206913 9 Manual.Count131072.C013941.packed 128 cuts13941 = true := by
 decide +kernel
def pointBounds13941 : List (Nat × Nat × Nat) := [(1831234560,95306477130115,95306854509689),(1831291904,95306883219477,95307260599332)]
theorem point_links_checked13941 : (cuts13941.take 2).map (fun c => (1831206913-1+2*2^9*c.k,95306273926998+c.lower,95306651306430+c.upper)) = pointBounds13941 := by
 decide +kernel
def cuts13942 : List PrefixCut := [⟨11,80999146,80999201⟩,
⟨67,491212879,491213221⟩,
⟨123,917397710,917398348⟩,
⟨128,953821824,953822487⟩]
theorem checked13942 : checkPrefixCuts (2^48) 1831337985 9 Manual.Count131072.C013942.packed 128 cuts13942 = true := by
 decide +kernel
def pointBounds13942 : List (Nat × Nat × Nat) := [(1831349248,95307290372106,95307667752247),(1831406592,95307700585839,95308077966267),(1831463936,95308126770670,95308504151394)]
theorem point_links_checked13942 : (cuts13942.take 3).map (fun c => (1831337985-1+2*2^9*c.k,95307209372960+c.lower,95307586753046+c.upper)) = pointBounds13942 := by
 decide +kernel
def cuts13943 : List PrefixCut := [⟨51,367001724,367001982⟩,
⟨107,780250556,780251099⟩,
⟨128,932084362,932085012⟩]
theorem checked13943 : checkPrefixCuts (2^48) 1831469057 9 Manual.Count131072.C013943.packed 128 cuts13943 = true := by
 decide +kernel
def pointBounds13943 : List (Nat × Nat × Nat) := [(1831521280,95308530196508,95308907577515),(1831578624,95308943445340,95309320826632)]
theorem point_links_checked13943 : (cuts13943.take 2).map (fun c => (1831469057-1+2*2^9*c.k,95308163194784+c.lower,95308540575533+c.upper)) = pointBounds13943 := by
 decide +kernel
def cuts13944 : List PrefixCut := [⟨35,256023456,256023635⟩,
⟨91,675546991,675547460⟩,
⟨128,953224401,953225064⟩]
theorem checked13944 : checkPrefixCuts (2^48) 1831600129 9 Manual.Count131072.C013944.packed 128 cuts13944 = true := by
 decide +kernel
def pointBounds13944 : List (Nat × Nat × Nat) := [(1831635968,95309351302602,95309728684180),(1831693312,95309770826137,95310148208005)]
theorem point_links_checked13944 : (cuts13944.take 2).map (fun c => (1831600129-1+2*2^9*c.k,95309095279146+c.lower,95309472660545+c.upper)) = pointBounds13944 := by
 decide +kernel
def cuts13945 : List PrefixCut := [⟨19,136608393,136608485⟩,
⟨75,554722681,554723058⟩,
⟨128,946548827,946549478⟩]
theorem checked13945 : checkPrefixCuts (2^48) 1831731201 9 Manual.Count131072.C013945.packed 128 cuts13945 = true := by
 decide +kernel
def pointBounds13945 : List (Nat × Nat × Nat) := [(1831750656,95310185111940,95310562494094),(1831808000,95310603226228,95310980608667)]
theorem point_links_checked13945 : (cuts13945.take 2).map (fun c => (1831731201-1+2*2^9*c.k,95310048503547+c.lower,95310425885609+c.upper)) = pointBounds13945 := by
 decide +kernel
def cuts13946 : List PrefixCut := [⟨3,23201893,23201909⟩,
⟨59,429612371,429612673⟩,
⟨115,855984430,855985025⟩,
⟨128,946481105,946481764⟩]
theorem checked13946 : checkPrefixCuts (2^48) 1831862273 9 Manual.Count131072.C013946.packed 128 cuts13946 = true := by
 decide +kernel
def pointBounds13946 : List (Nat × Nat × Nat) := [(1831865344,95311018254267,95311395636996),(1831922688,95311424664745,95311802047760),(1831980032,95311851036804,95312228420112)]
theorem point_links_checked13946 : (cuts13946.take 3).map (fun c => (1831862273-1+2*2^9*c.k,95310995052374+c.lower,95311372435087+c.upper)) = pointBounds13946 := by
 decide +kernel
def cuts13947 : List PrefixCut := [⟨43,324338690,324338915⟩,
⟨99,729174642,729175145⟩,
⟨128,943955404,943956053⟩]
theorem checked13947 : checkPrefixCuts (2^48) 1831993345 9 Manual.Count131072.C013947.packed 128 cuts13947 = true := by
 decide +kernel
def pointBounds13947 : List (Nat × Nat × Nat) := [(1832037376,95312265872169,95312643255766),(1832094720,95312670708121,95313048091996)]
theorem point_links_checked13947 : (cuts13947.take 2).map (fun c => (1831993345-1+2*2^9*c.k,95311941533479+c.lower,95312318916851+c.upper)) = pointBounds13947 := by
 decide +kernel
def cuts13948 : List PrefixCut := [⟨27,191732611,191732740⟩,
⟨83,608833485,608833905⟩,
⟨128,939125050,939125700⟩]
theorem checked13948 : checkPrefixCuts (2^48) 1832124417 9 Manual.Count131072.C013948.packed 128 cuts13948 = true := by
 decide +kernel
def pointBounds13948 : List (Nat × Nat × Nat) := [(1832152064,95313077221494,95313454605644),(1832209408,95313494322368,95313871706809)]
theorem point_links_checked13948 : (cuts13948.take 2).map (fun c => (1832124417-1+2*2^9*c.k,95312885488883+c.lower,95313262872904+c.upper)) = pointBounds13948 := by
 decide +kernel
def cuts13949 : List PrefixCut := [⟨11,78193398,78193454⟩,
⟨67,485743867,485744211⟩,
⟨123,900655075,900655707⟩,
⟨128,936753727,936754385⟩]
theorem checked13949 : checkPrefixCuts (2^48) 1832255489 9 Manual.Count131072.C013949.packed 128 cuts13949 = true := by
 decide +kernel
def pointBounds13949 : List (Nat × Nat × Nat) := [(1832266752,95313902807331,95314280192058),(1832324096,95314310357800,95314687742815),(1832381440,95314725269008,95315102654311)]
theorem point_links_checked13949 : (cuts13949.take 3).map (fun c => (1832255489-1+2*2^9*c.k,95313824613933+c.lower,95314201998604+c.upper)) = pointBounds13949 := by
 decide +kernel
def cuts13950 : List PrefixCut := [⟨51,377724218,377724484⟩,
⟨107,798907071,798907626⟩,
⟨128,950357636,950358298⟩]
theorem checked13950 : checkPrefixCuts (2^48) 1832386561 9 Manual.Count131072.C013950.packed 128 cuts13950 = true := by
 decide +kernel
def pointBounds13950 : List (Nat × Nat × Nat) := [(1832438784,95315139091878,95315516477473),(1832496128,95315560274731,95315937660615)]
theorem point_links_checked13950 : (cuts13950.take 2).map (fun c => (1832386561-1+2*2^9*c.k,95314761367660+c.lower,95315138752989+c.upper)) = pointBounds13950 := by
 decide +kernel
def cuts13951 : List PrefixCut := [⟨35,255588044,255588219⟩,
⟨91,656470141,656470598⟩,
⟨128,931858301,931858946⟩]
theorem checked13951 : checkPrefixCuts (2^48) 1832517633 9 Manual.Count131072.C013951.packed 128 cuts13951 = true := by
 decide +kernel
def pointBounds13951 : List (Nat × Nat × Nat) := [(1832553472,95315967313340,95316344699506),(1832610816,95316368195437,95316745581885)]
theorem point_links_checked13951 : (cuts13951.take 2).map (fun c => (1832517633-1+2*2^9*c.k,95315711725296+c.lower,95316089111287+c.upper)) = pointBounds13951 := by
 decide +kernel
def cuts13952 : List PrefixCut := [⟨19,140686876,140686973⟩,
⟨75,548455213,548455594⟩,
⟨128,937013515,937014166⟩]
theorem checked13952 : checkPrefixCuts (2^48) 1832648705 9 Manual.Count131072.C013952.packed 128 cuts13952 = true := by
 decide +kernel
def pointBounds13952 : List (Nat × Nat × Nat) := [(1832668160,95316784270473,95317161657206),(1832725504,95317192038810,95317569425827)]
theorem point_links_checked13952 : (cuts13952.take 2).map (fun c => (1832648705-1+2*2^9*c.k,95316643583597+c.lower,95317020970233+c.upper)) = pointBounds13952 := by
 decide +kernel
def cuts13953 : List PrefixCut := [⟨3,20579452,20579467⟩,
⟨59,432008084,432008387⟩,
⟨115,845420374,845420960⟩,
⟨128,942168032,942168684⟩]
theorem checked13953 : checkPrefixCuts (2^48) 1832779777 9 Manual.Count131072.C013953.packed 128 cuts13953 = true := by
 decide +kernel
def pointBounds13953 : List (Nat × Nat × Nat) := [(1832782848,95317601176564,95317978563866),(1832840192,95318012605196,95318389992786),(1832897536,95318426017486,95318803405359)]
theorem point_links_checked13953 : (cuts13953.take 3).map (fun c => (1832779777-1+2*2^9*c.k,95317580597112+c.lower,95317957984399+c.upper)) = pointBounds13953 := by
 decide +kernel
def cuts13954 : List PrefixCut := [⟨43,311123289,311123503⟩,
⟨99,720977607,720978107⟩,
⟨128,937493548,937494198⟩]
theorem checked13954 : checkPrefixCuts (2^48) 1832910849 9 Manual.Count131072.C013954.packed 128 cuts13954 = true := by
 decide +kernel
def pointBounds13954 : List (Nat × Nat × Nat) := [(1832954880,95318833888433,95319211276586),(1833012224,95319243742751,95319621131190)]
theorem point_links_checked13954 : (cuts13954.take 2).map (fun c => (1832910849-1+2*2^9*c.k,95318522765144+c.lower,95318900153083+c.upper)) = pointBounds13954 := by
 decide +kernel
def cuts13955 : List PrefixCut := [⟨27,199467942,199468084⟩,
⟨83,619584672,619585105⟩,
⟨128,953089017,953089678⟩]
theorem checked13955 : checkPrefixCuts (2^48) 1833041921 9 Manual.Count131072.C013955.packed 128 cuts13955 = true := by
 decide +kernel
def pointBounds13955 : List (Nat × Nat × Nat) := [(1833069568,95319659726634,95320037115365),(1833126912,95320079843364,95320457232386)]
theorem point_links_checked13955 : (cuts13955.take 2).map (fun c => (1833041921-1+2*2^9*c.k,95319460258692+c.lower,95319837647281+c.upper)) = pointBounds13955 := by
 decide +kernel
def cuts13956 : List PrefixCut := [⟨11,81378700,81378757⟩,
⟨67,496095176,496095525⟩,
⟨123,909723979,909724611⟩,
⟨128,949028788,949029446⟩]
theorem checked13956 : checkPrefixCuts (2^48) 1833172993 9 Manual.Count131072.C013956.packed 128 cuts13956 = true := by
 decide +kernel
def pointBounds13956 : List (Nat × Nat × Nat) := [(1833184256,95320494726409,95320872115716),(1833241600,95320909442885,95321286832484),(1833298944,95321323071688,95321700461570)]
theorem point_links_checked13956 : (cuts13956.take 3).map (fun c => (1833172993-1+2*2^9*c.k,95320413347709+c.lower,95320790736959+c.upper)) = pointBounds13956 := by
 decide +kernel
def cuts13957 : List PrefixCut := [⟨51,380145288,380145554⟩,
⟨107,791905916,791906475⟩,
⟨128,950496343,950497015⟩]
theorem checked13957 : checkPrefixCuts (2^48) 1833304065 9 Manual.Count131072.C013957.packed 128 cuts13957 = true := by
 decide +kernel
def pointBounds13957 : List (Nat × Nat × Nat) := [(1833356288,95321742521785,95322119911959),(1833413632,95322154282413,95322531672880)]
theorem point_links_checked13957 : (cuts13957.take 2).map (fun c => (1833304065-1+2*2^9*c.k,95321362376497+c.lower,95321739766405+c.upper)) = pointBounds13957 := by
 decide +kernel
def cuts13958 : List PrefixCut := [⟨35,264978483,264978667⟩,
⟨91,689915843,689916320⟩,
⟨128,959639656,959640321⟩]
theorem checked13958 : checkPrefixCuts (2^48) 1833435137 9 Manual.Count131072.C013958.packed 128 cuts13958 = true := by
 decide +kernel
def pointBounds13958 : List (Nat × Nat × Nat) := [(1833470976,95322577851323,95322955242087),(1833528320,95323002788683,95323380179740)]
theorem point_links_checked13958 : (cuts13958.take 2).map (fun c => (1833435137-1+2*2^9*c.k,95322312872840+c.lower,95322690263420+c.upper)) = pointBounds13958 := by
 decide +kernel
def cuts13959 : List PrefixCut := [⟨19,139234884,139234980⟩,
⟨75,561536014,561536404⟩,
⟨128,951281513,951282172⟩]
theorem checked13959 : checkPrefixCuts (2^48) 1833566209 9 Manual.Count131072.C013959.packed 128 cuts13959 = true := by
 decide +kernel
def pointBounds13959 : List (Nat × Nat × Nat) := [(1833585664,95323411747380,95323789138721),(1833643008,95323834048510,95324211440145)]
theorem point_links_checked13959 : (cuts13959.take 2).map (fun c => (1833566209-1+2*2^9*c.k,95323272512496+c.lower,95323649903741+c.upper)) = pointBounds13959 := by
 decide +kernel
def cuts13960 : List PrefixCut := [⟨3,22718171,22718187⟩,
⟨59,435782927,435783228⟩,
⟨115,851137242,851137829⟩,
⟨128,943078268,943078919⟩]
theorem checked13960 : checkPrefixCuts (2^48) 1833697281 9 Manual.Count131072.C013960.packed 128 cuts13960 = true := by
 decide +kernel
def pointBounds13960 : List (Nat × Nat × Nat) := [(1833700352,95324246512180,95324623904100),(1833757696,95324659576936,95325036969141),(1833815040,95325074931251,95325452323742)]
theorem point_links_checked13960 : (cuts13960.take 3).map (fun c => (1833697281-1+2*2^9*c.k,95324223794009+c.lower,95324601185913+c.upper)) = pointBounds13960 := by
 decide +kernel
def cuts13961 : List PrefixCut := [⟨43,329846705,329846934⟩,
⟨99,740877502,740878016⟩,
⟨128,954061996,954062660⟩]
theorem checked13961 : checkPrefixCuts (2^48) 1833828353 9 Manual.Count131072.C013961.packed 128 cuts13961 = true := by
 decide +kernel
def pointBounds13961 : List (Nat × Nat × Nat) := [(1833872384,95325496718982,95325874111766),(1833929728,95325907749779,95326285142848)]
theorem point_links_checked13961 : (cuts13961.take 2).map (fun c => (1833828353-1+2*2^9*c.k,95325166872277+c.lower,95325544264832+c.upper)) = pointBounds13961 := by
 decide +kernel
def cuts13962 : List PrefixCut := [⟨27,202898171,202898314⟩,
⟨83,620349132,620349566⟩,
⟨128,944938836,944939498⟩]
theorem checked13962 : checkPrefixCuts (2^48) 1833959425 9 Manual.Count131072.C013962.packed 128 cuts13962 = true := by
 decide +kernel
def pointBounds13962 : List (Nat × Nat × Nat) := [(1833987072,95326323832444,95326701225806),(1834044416,95326741283405,95327118677058)]
theorem point_links_checked13962 : (cuts13962.take 2).map (fun c => (1833959425-1+2*2^9*c.k,95326120934273+c.lower,95326498327492+c.upper)) = pointBounds13962 := by
 decide +kernel
def cuts13963 : List PrefixCut := [⟨11,79956770,79956825⟩,
⟨67,492163798,492164139⟩,
⟨123,898066172,898066796⟩,
⟨128,935663288,935663937⟩]
theorem checked13963 : checkPrefixCuts (2^48) 1834090497 9 Manual.Count131072.C013963.packed 128 cuts13963 = true := by
 decide +kernel
def pointBounds13963 : List (Nat × Nat × Nat) := [(1834101760,95327145829879,95327523223815),(1834159104,95327558036907,95327935431129),(1834216448,95327963939281,95328341333786)]
theorem point_links_checked13963 : (cuts13963.take 3).map (fun c => (1834090497-1+2*2^9*c.k,95327065873109+c.lower,95327443266990+c.upper)) = pointBounds13963 := by
 decide +kernel
def cuts13964 : List PrefixCut := [⟨51,373203102,373203361⟩,
⟨107,784911175,784911720⟩,
⟨128,945723956,945724612⟩]
theorem checked13964 : checkPrefixCuts (2^48) 1834221569 9 Manual.Count131072.C013964.packed 128 cuts13964 = true := by
 decide +kernel
def pointBounds13964 : List (Nat × Nat × Nat) := [(1834273792,95328374739499,95328752134288),(1834331136,95328786447572,95329163842647)]
theorem point_links_checked13964 : (cuts13964.take 2).map (fun c => (1834221569-1+2*2^9*c.k,95328001536397+c.lower,95328378930927+c.upper)) = pointBounds13964 := by
 decide +kernel
def cuts13965 : List PrefixCut := [⟨35,260089142,260089326⟩,
⟨91,677602191,677602660⟩,
⟨128,954862989,954863650⟩]
theorem checked13965 : checkPrefixCuts (2^48) 1834352641 9 Manual.Count131072.C013965.packed 128 cuts13965 = true := by
 decide +kernel
def pointBounds13965 : List (Nat × Nat × Nat) := [(1834388480,95329207349495,95329584744865),(1834445824,95329624862544,95330002258199)]
theorem point_links_checked13965 : (cuts13965.take 2).map (fun c => (1834352641-1+2*2^9*c.k,95328947260353+c.lower,95329324655539+c.upper)) = pointBounds13965 := by
 decide +kernel
def cuts13966 : List PrefixCut := [⟨19,141466751,141466849⟩,
⟨75,543457113,543457491⟩,
⟨128,926256896,926257539⟩]
theorem checked13966 : checkPrefixCuts (2^48) 1834483713 9 Manual.Count131072.C013966.packed 128 cuts13966 = true := by
 decide +kernel
def pointBounds13966 : List (Nat × Nat × Nat) := [(1834503168,95330043590093,95330420986038),(1834560512,95330445580455,95330822976680)]
theorem point_links_checked13966 : (cuts13966.take 2).map (fun c => (1834483713-1+2*2^9*c.k,95329902123342+c.lower,95330279519189+c.upper)) = pointBounds13966 := by
 decide +kernel
def cuts13967 : List PrefixCut := [⟨3,23013656,23013672⟩,
⟨59,436332176,436332478⟩,
⟨115,841966865,841967445⟩,
⟨128,936163128,936163773⟩]
theorem checked13967 : checkPrefixCuts (2^48) 1834614785 9 Manual.Count131072.C013967.packed 128 cuts13967 = true := by
 decide +kernel
def pointBounds13967 : List (Nat × Nat × Nat) := [(1834617856,95330851393894,95331228790400),(1834675200,95331264712414,95331642109206),(1834732544,95331670347103,95332047744173)]
theorem point_links_checked13967 : (cuts13967.take 3).map (fun c => (1834614785-1+2*2^9*c.k,95330828380238+c.lower,95331205776728+c.upper)) = pointBounds13967 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000123
