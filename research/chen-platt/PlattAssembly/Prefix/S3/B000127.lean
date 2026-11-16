import PlattAssemblyKernel
import PlattCertificates.Count131072.C024064
import PlattCertificates.Count131072.C024065
import PlattCertificates.Count131072.C024066
import PlattCertificates.Count131072.C024067
import PlattCertificates.Count131072.C024068
import PlattCertificates.Count131072.C024069
import PlattCertificates.Count131072.C024070
import PlattCertificates.Count131072.C024071
import PlattCertificates.Count131072.C024072
import PlattCertificates.Count131072.C024073
import PlattCertificates.Count131072.C024074
import PlattCertificates.Count131072.C024075
import PlattCertificates.Count131072.C024076
import PlattCertificates.Count131072.C024077
import PlattCertificates.Count131072.C024078
import PlattCertificates.Count131072.C024079
import PlattCertificates.Count131072.C024080
import PlattCertificates.Count131072.C024081
import PlattCertificates.Count131072.C024082
import PlattCertificates.Count131072.C024083
import PlattCertificates.Count131072.C024084
import PlattCertificates.Count131072.C024085
import PlattCertificates.Count131072.C024086
import PlattCertificates.Count131072.C024087
import PlattCertificates.Count131072.C024088
import PlattCertificates.Count131072.C024089
import PlattCertificates.Count131072.C024090
import PlattCertificates.Count131072.C024091
import PlattCertificates.Count131072.C024092
import PlattCertificates.Count131072.C024093
import PlattCertificates.Count131072.C024094
import PlattCertificates.Count131072.C024095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24064 : List PrefixCut := [⟨26,108737370,108737434⟩,
⟨123,511235861,511236159⟩,
⟨128,533249919,533250229⟩]
theorem checked24064 : checkPrefixCuts (2^48) 3158048769 9 Manual.Count131072.C024064.packed 128 cuts24064 = true := by
 decide +kernel
def pointBounds24064 : List (Nat × Nat × Nat) := [(3158075392,102408155196558,102408536937125),(3158174720,102408557695049,102408939435850)]
theorem point_links_checked24064 : (cuts24064.take 2).map (fun c => (3158048769-1+2*2^9*c.k,102408046459188+c.lower,102408428199691+c.upper)) = pointBounds24064 := by
 decide +kernel
def cuts24065 : List PrefixCut := [⟨92,381184818,381185042⟩,
⟨128,533316910,533317221⟩]
theorem checked24065 : checkPrefixCuts (2^48) 3158179841 9 Manual.Count131072.C024065.packed 128 cuts24065 = true := by
 decide +kernel
def pointBounds24065 : List (Nat × Nat × Nat) := [(3158274048,102408960893925,102409342634962)]
theorem point_links_checked24065 : (cuts24065.take 1).map (fun c => (3158179841-1+2*2^9*c.k,102408579709107+c.lower,102408961449920+c.upper)) = pointBounds24065 := by
 decide +kernel
def cuts24066 : List PrefixCut := [⟨61,251232372,251232513⟩,
⟨128,534720659,534720956⟩]
theorem checked24066 : checkPrefixCuts (2^48) 3158310913 9 Manual.Count131072.C024066.packed 128 cuts24066 = true := by
 decide +kernel
def pointBounds24066 : List (Nat × Nat × Nat) := [(3158373376,102409364258389,102409745999654)]
theorem point_links_checked24066 : (cuts24066.take 1).map (fun c => (3158310913-1+2*2^9*c.k,102409113026017+c.lower,102409494767141+c.upper)) = pointBounds24066 := by
 decide +kernel
def cuts24067 : List PrefixCut := [⟨30,124052043,124052112⟩,
⟨127,522757110,522757403⟩,
⟨128,526589037,526589333⟩]
theorem checked24067 : checkPrefixCuts (2^48) 3158441985 9 Manual.Count131072.C024067.packed 128 cuts24067 = true := by
 decide +kernel
def pointBounds24067 : List (Nat × Nat × Nat) := [(3158472704,102409771798719,102410153540209),(3158572032,102410170503786,102410552245500)]
theorem point_links_checked24067 : (cuts24067.take 2).map (fun c => (3158441985-1+2*2^9*c.k,102409647746676+c.lower,102410029488097+c.upper)) = pointBounds24067 := by
 decide +kernel
def cuts24068 : List PrefixCut := [⟨96,403058961,403059182⟩,
⟨128,536725974,536726270⟩]
theorem checked24068 : checkPrefixCuts (2^48) 3158573057 9 Manual.Count131072.C024068.packed 128 cuts24068 = true := by
 decide +kernel
def pointBounds24068 : List (Nat × Nat × Nat) := [(3158671360,102410577394674,102410959136612)]
theorem point_links_checked24068 : (cuts24068.take 1).map (fun c => (3158573057-1+2*2^9*c.k,102410174335713+c.lower,102410556077430+c.upper)) = pointBounds24068 := by
 decide +kernel
def cuts24069 : List PrefixCut := [⟨65,270448694,270448847⟩,
⟨128,534475979,534476274⟩]
theorem checked24069 : checkPrefixCuts (2^48) 3158704129 9 Manual.Count131072.C024069.packed 128 cuts24069 = true := by
 decide +kernel
def pointBounds24069 : List (Nat × Nat × Nat) := [(3158770688,102410981510381,102411363252547)]
theorem point_links_checked24069 : (cuts24069.take 1).map (fun c => (3158704129-1+2*2^9*c.k,102410711061687+c.lower,102411092803700+c.upper)) = pointBounds24069 := by
 decide +kernel
def cuts24070 : List PrefixCut := [⟨34,142570695,142570775⟩,
⟨128,544522586,544522889⟩]
theorem checked24070 : checkPrefixCuts (2^48) 3158835201 9 Manual.Count131072.C024070.packed 128 cuts24070 = true := by
 decide +kernel
def pointBounds24070 : List (Nat × Nat × Nat) := [(3158870016,102411388108361,102411769850749)]
theorem point_links_checked24070 : (cuts24070.take 1).map (fun c => (3158835201-1+2*2^9*c.k,102411245537666+c.lower,102411627279974+c.upper)) = pointBounds24070 := by
 decide +kernel
def cuts24071 : List PrefixCut := [⟨3,11672550,11672558⟩,
⟨100,416017413,416017645⟩,
⟨128,532471358,532471653⟩]
theorem checked24071 : checkPrefixCuts (2^48) 3158966273 9 Manual.Count131072.C024071.packed 128 cuts24071 = true := by
 decide +kernel
def pointBounds24071 : List (Nat × Nat × Nat) := [(3158969344,102411801732802,102412183475421),(3159068672,102412206077665,102412587820508)]
theorem point_links_checked24071 : (cuts24071.take 2).map (fun c => (3158966273-1+2*2^9*c.k,102411790060252+c.lower,102412171802863+c.upper)) = pointBounds24071 := by
 decide +kernel
def cuts24072 : List PrefixCut := [⟨69,284136067,284136226⟩,
⟨128,528974433,528974729⟩]
theorem checked24072 : checkPrefixCuts (2^48) 3159097345 9 Manual.Count131072.C024072.packed 128 cuts24072 = true := by
 decide +kernel
def pointBounds24072 : List (Nat × Nat × Nat) := [(3159168000,102412606667677,102412988410742)]
theorem point_links_checked24072 : (cuts24072.take 1).map (fun c => (3159097345-1+2*2^9*c.k,102412322531610+c.lower,102412704274516+c.upper)) = pointBounds24072 := by
 decide +kernel
def cuts24073 : List PrefixCut := [⟨38,153066147,153066232⟩,
⟨128,533941687,533941985⟩]
theorem checked24073 : checkPrefixCuts (2^48) 3159228417 9 Manual.Count131072.C024073.packed 128 cuts24073 = true := by
 decide +kernel
def pointBounds24073 : List (Nat × Nat × Nat) := [(3159267328,102413004572190,102413386315477)]
theorem point_links_checked24073 : (cuts24073.take 1).map (fun c => (3159228417-1+2*2^9*c.k,102412851506043+c.lower,102413233249245+c.upper)) = pointBounds24073 := by
 decide +kernel
def cuts24074 : List PrefixCut := [⟨7,28687719,28687735⟩,
⟨104,434228986,434229236⟩,
⟨128,531870565,531870872⟩]
theorem checked24074 : checkPrefixCuts (2^48) 3159359489 9 Manual.Count131072.C024074.packed 128 cuts24074 = true := by
 decide +kernel
def pointBounds24074 : List (Nat × Nat × Nat) := [(3159366656,102413414135449,102413795878965),(3159465984,102413819676716,102414201420466)]
theorem point_links_checked24074 : (cuts24074.take 2).map (fun c => (3159359489-1+2*2^9*c.k,102413385447730+c.lower,102413767191230+c.upper)) = pointBounds24074 := by
 decide +kernel
def cuts24075 : List PrefixCut := [⟨73,301561672,301561848⟩,
⟨128,528374105,528374407⟩]
theorem checked24075 : checkPrefixCuts (2^48) 3159490561 9 Manual.Count131072.C024075.packed 128 cuts24075 = true := by
 decide +kernel
def pointBounds24075 : List (Nat × Nat × Nat) := [(3159565312,102414218879967,102414600623950)]
theorem point_links_checked24075 : (cuts24075.take 1).map (fun c => (3159490561-1+2*2^9*c.k,102413917318295+c.lower,102414299062102+c.upper)) = pointBounds24075 := by
 decide +kernel
def cuts24076 : List PrefixCut := [⟨42,175407160,175407262⟩,
⟨128,530757456,530757757⟩]
theorem checked24076 : checkPrefixCuts (2^48) 3159621633 9 Manual.Count131072.C024076.packed 128 cuts24076 = true := by
 decide +kernel
def pointBounds24076 : List (Nat × Nat × Nat) := [(3159664640,102414621099560,102415002843771)]
theorem point_links_checked24076 : (cuts24076.take 1).map (fun c => (3159621633-1+2*2^9*c.k,102414445692400+c.lower,102414827436509+c.upper)) = pointBounds24076 := by
 decide +kernel
def cuts24077 : List PrefixCut := [⟨11,46054957,46054984⟩,
⟨108,454930260,454930515⟩,
⟨128,538396257,538396560⟩]
theorem checked24077 : checkPrefixCuts (2^48) 3159752705 9 Manual.Count131072.C024077.packed 128 cuts24077 = true := by
 decide +kernel
def pointBounds24077 : List (Nat × Nat × Nat) := [(3159763968,102415022504813,102415404249250),(3159863296,102415431380116,102415813124781)]
theorem point_links_checked24077 : (cuts24077.take 2).map (fun c => (3159752705-1+2*2^9*c.k,102414976449856+c.lower,102415358194266+c.upper)) = pointBounds24077 := by
 decide +kernel
def cuts24078 : List PrefixCut := [⟨77,320942639,320942821⟩,
⟨128,530891569,530891864⟩]
theorem checked24078 : checkPrefixCuts (2^48) 3159883777 9 Manual.Count131072.C024078.packed 128 cuts24078 = true := by
 decide +kernel
def pointBounds24078 : List (Nat × Nat × Nat) := [(3159962624,102415835788752,102416217533647)]
theorem point_links_checked24078 : (cuts24078.take 1).map (fun c => (3159883777-1+2*2^9*c.k,102415514846113+c.lower,102415896590826+c.upper)) = pointBounds24078 := by
 decide +kernel
def cuts24079 : List PrefixCut := [⟨46,191062133,191062242⟩,
⟨128,530602279,530602587⟩]
theorem checked24079 : checkPrefixCuts (2^48) 3160014849 9 Manual.Count131072.C024079.packed 128 cuts24079 = true := by
 decide +kernel
def pointBounds24079 : List (Nat × Nat × Nat) := [(3160061952,102416236799815,102416618544932)]
theorem point_links_checked24079 : (cuts24079.take 1).map (fun c => (3160014849-1+2*2^9*c.k,102416045737682+c.lower,102416427482690+c.upper)) = pointBounds24079 := by
 decide +kernel
def cuts24080 : List PrefixCut := [⟨15,59944107,59944141⟩,
⟨112,460306516,460306777⟩,
⟨128,528264454,528264755⟩]
theorem checked24080 : checkPrefixCuts (2^48) 3160145921 9 Manual.Count131072.C024080.packed 128 cuts24080 = true := by
 decide +kernel
def pointBounds24080 : List (Nat × Nat × Nat) := [(3160161280,102416636284068,102417018029418),(3160260608,102417036646477,102417418392054)]
theorem point_links_checked24080 : (cuts24080.take 2).map (fun c => (3160145921-1+2*2^9*c.k,102416576339961+c.lower,102416958085277+c.upper)) = pointBounds24080 := by
 decide +kernel
def cuts24081 : List PrefixCut := [⟨81,344148539,344148731⟩,
⟨128,542403936,542404236⟩]
theorem checked24081 : checkPrefixCuts (2^48) 3160276993 9 Manual.Count131072.C024081.packed 128 cuts24081 = true := by
 decide +kernel
def pointBounds24081 : List (Nat × Nat × Nat) := [(3160359936,102417448752954,102417830498763)]
theorem point_links_checked24081 : (cuts24081.take 1).map (fun c => (3160276993-1+2*2^9*c.k,102417104604415+c.lower,102417486350032+c.upper)) = pointBounds24081 := by
 decide +kernel
def cuts24082 : List PrefixCut := [⟨50,209295958,209296080⟩,
⟨128,534633110,534633419⟩]
theorem checked24082 : checkPrefixCuts (2^48) 3160408065 9 Manual.Count131072.C024082.packed 128 cuts24082 = true := by
 decide +kernel
def pointBounds24082 : List (Nat × Nat × Nat) := [(3160459264,102417856304309,102418238050348)]
theorem point_links_checked24082 : (cuts24082.take 1).map (fun c => (3160408065-1+2*2^9*c.k,102417647008351+c.lower,102418028754268+c.upper)) = pointBounds24082 := by
 decide +kernel
def cuts24083 : List PrefixCut := [⟨19,81577922,81577968⟩,
⟨116,487055341,487055621⟩,
⟨128,537015544,537015851⟩]
theorem checked24083 : checkPrefixCuts (2^48) 3160539137 9 Manual.Count131072.C024083.packed 128 cuts24083 = true := by
 decide +kernel
def pointBounds24083 : List (Nat × Nat × Nat) := [(3160558592,102418263219383,102418644965655),(3160657920,102418668696802,102419050443308)]
theorem point_links_checked24083 : (cuts24083.take 2).map (fun c => (3160539137-1+2*2^9*c.k,102418181641461+c.lower,102418563387687+c.upper)) = pointBounds24083 := by
 decide +kernel
def cuts24084 : List PrefixCut := [⟨85,355148218,355148422⟩,
⟨128,536993181,536993485⟩]
theorem checked24084 : checkPrefixCuts (2^48) 3160670209 9 Manual.Count131072.C024084.packed 128 cuts24084 = true := by
 decide +kernel
def pointBounds24084 : List (Nat × Nat × Nat) := [(3160757248,102419073805223,102419455551960)]
theorem point_links_checked24084 : (cuts24084.take 1).map (fun c => (3160670209-1+2*2^9*c.k,102418718657005+c.lower,102419100403538+c.upper)) = pointBounds24084 := by
 decide +kernel
def cuts24085 : List PrefixCut := [⟨54,225298943,225299072⟩,
⟨128,532607462,532607769⟩]
theorem checked24085 : checkPrefixCuts (2^48) 3160801281 9 Manual.Count131072.C024085.packed 128 cuts24085 = true := by
 decide +kernel
def pointBounds24085 : List (Nat × Nat × Nat) := [(3160856576,102419480949129,102419862696095)]
theorem point_links_checked24085 : (cuts24085.take 1).map (fun c => (3160801281-1+2*2^9*c.k,102419255650186+c.lower,102419637397023+c.upper)) = pointBounds24085 := by
 decide +kernel
def cuts24086 : List PrefixCut := [⟨23,93411073,93411125⟩,
⟨120,497679941,497680217⟩,
⟨128,529824998,529825293⟩]
theorem checked24086 : checkPrefixCuts (2^48) 3160932353 9 Manual.Count131072.C024086.packed 128 cuts24086 = true := by
 decide +kernel
def pointBounds24086 : List (Nat × Nat × Nat) := [(3160955904,102419881668721,102420263415917),(3161055232,102420285937589,102420667685009)]
theorem point_links_checked24086 : (cuts24086.take 2).map (fun c => (3160932353-1+2*2^9*c.k,102419788257648+c.lower,102420170004792+c.upper)) = pointBounds24086 := by
 decide +kernel
def cuts24087 : List PrefixCut := [⟨89,373268596,373268807⟩,
⟨128,537638721,537639026⟩]
theorem checked24087 : checkPrefixCuts (2^48) 3161063425 9 Manual.Count131072.C024087.packed 128 cuts24087 = true := by
 decide +kernel
def pointBounds24087 : List (Nat × Nat × Nat) := [(3161154560,102420691351242,102421073098892)]
theorem point_links_checked24087 : (cuts24087.take 1).map (fun c => (3161063425-1+2*2^9*c.k,102420318082646+c.lower,102420699830085+c.upper)) = pointBounds24087 := by
 decide +kernel
def cuts24088 : List PrefixCut := [⟨58,237736391,237736530⟩,
⟨128,534232930,534233237⟩]
theorem checked24088 : checkPrefixCuts (2^48) 3161194497 9 Manual.Count131072.C024088.packed 128 cuts24088 = true := by
 decide +kernel
def pointBounds24088 : List (Nat × Nat × Nat) := [(3161253888,102421093457758,102421475205641)]
theorem point_links_checked24088 : (cuts24088.take 1).map (fun c => (3161194497-1+2*2^9*c.k,102420855721367+c.lower,102421237469111+c.upper)) = pointBounds24088 := by
 decide +kernel
def cuts24089 : List PrefixCut := [⟨27,112097059,112097122⟩,
⟨124,516582144,516582439⟩,
⟨128,533409446,533409752⟩]
theorem checked24089 : checkPrefixCuts (2^48) 3161325569 9 Manual.Count131072.C024089.packed 128 cuts24089 = true := by
 decide +kernel
def pointBounds24089 : List (Nat × Nat × Nat) := [(3161353216,102421502051356,102421883799470),(3161452544,102421906536441,102422288284787)]
theorem point_links_checked24089 : (cuts24089.take 2).map (fun c => (3161325569-1+2*2^9*c.k,102421389954297+c.lower,102421771702348+c.upper)) = pointBounds24089 := by
 decide +kernel
def cuts24090 : List PrefixCut := [⟨93,384529114,384529326⟩,
⟨128,532942288,532942586⟩]
theorem checked24090 : checkPrefixCuts (2^48) 3161456641 9 Manual.Count131072.C024090.packed 128 cuts24090 = true := by
 decide +kernel
def pointBounds24090 : List (Nat × Nat × Nat) := [(3161551872,102422307892857,102422689641426)]
theorem point_links_checked24090 : (cuts24090.take 1).map (fun c => (3161456641-1+2*2^9*c.k,102421923363743+c.lower,102422305112100+c.upper)) = pointBounds24090 := by
 decide +kernel
def cuts24091 : List PrefixCut := [⟨62,259518677,259518825⟩,
⟨128,532920140,532920448⟩]
theorem checked24091 : checkPrefixCuts (2^48) 3161587713 9 Manual.Count131072.C024091.packed 128 cuts24091 = true := by
 decide +kernel
def pointBounds24091 : List (Nat × Nat × Nat) := [(3161651200,102422715824708,102423097573511)]
theorem point_links_checked24091 : (cuts24091.take 1).map (fun c => (3161587713-1+2*2^9*c.k,102422456306031+c.lower,102422838054686+c.upper)) = pointBounds24091 := by
 decide +kernel
def cuts24092 : List PrefixCut := [⟨31,131223538,131223610⟩,
⟨128,531117602,531117896⟩]
theorem checked24092 : checkPrefixCuts (2^48) 3161718785 9 Manual.Count131072.C024092.packed 128 cuts24092 = true := by
 decide +kernel
def pointBounds24092 : List (Nat × Nat × Nat) := [(3161750528,102423120449709,102423502198744),(3161849856,102423520343773,102423902093030)]
theorem point_links_checked24092 : (cuts24092.take 2).map (fun c => (3161718785-1+2*2^9*c.k,102422989226171+c.lower,102423370975134+c.upper)) = pointBounds24092 := by
 decide +kernel
def cuts24093 : List PrefixCut := [⟨97,401216824,401217059⟩,
⟨128,530917463,530917772⟩]
theorem checked24093 : checkPrefixCuts (2^48) 3161849857 9 Manual.Count131072.C024093.packed 128 cuts24093 = true := by
 decide +kernel
def pointBounds24093 : List (Nat × Nat × Nat) := [(3161949184,102423921560597,102424303310089)]
theorem point_links_checked24093 : (cuts24093.take 1).map (fun c => (3161849857-1+2*2^9*c.k,102423520343773+c.lower,102423902093030+c.upper)) = pointBounds24093 := by
 decide +kernel
def cuts24094 : List PrefixCut := [⟨66,274975297,274975450⟩,
⟨128,533565998,533566295⟩]
theorem checked24094 : checkPrefixCuts (2^48) 3161980929 9 Manual.Count131072.C024094.packed 128 cuts24094 = true := by
 decide +kernel
def pointBounds24094 : List (Nat × Nat × Nat) := [(3162048512,102424326236533,102424707986252)]
theorem point_links_checked24094 : (cuts24094.take 1).map (fun c => (3161980929-1+2*2^9*c.k,102424051261236+c.lower,102424433010802+c.upper)) = pointBounds24094 := by
 decide +kernel
def cuts24095 : List PrefixCut := [⟨35,146250556,146250640⟩,
⟨128,532653770,532654069⟩]
theorem checked24095 : checkPrefixCuts (2^48) 3162112001 9 Manual.Count131072.C024095.packed 128 cuts24095 = true := by
 decide +kernel
def pointBounds24095 : List (Nat × Nat × Nat) := [(3162147840,102424731077790,102425112827737)]
theorem point_links_checked24095 : (cuts24095.take 1).map (fun c => (3162112001-1+2*2^9*c.k,102424584827234+c.lower,102424966577097+c.upper)) = pointBounds24095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000127
