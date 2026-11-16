import PlattAssemblyKernel
import PlattCertificates.Count131072.C028128
import PlattCertificates.Count131072.C028129
import PlattCertificates.Count131072.C028130
import PlattCertificates.Count131072.C028131
import PlattCertificates.Count131072.C028132
import PlattCertificates.Count131072.C028133
import PlattCertificates.Count131072.C028134
import PlattCertificates.Count131072.C028135
import PlattCertificates.Count131072.C028136
import PlattCertificates.Count131072.C028137
import PlattCertificates.Count131072.C028138
import PlattCertificates.Count131072.C028139
import PlattCertificates.Count131072.C028140
import PlattCertificates.Count131072.C028141
import PlattCertificates.Count131072.C028142
import PlattCertificates.Count131072.C028143
import PlattCertificates.Count131072.C028144
import PlattCertificates.Count131072.C028145
import PlattCertificates.Count131072.C028146
import PlattCertificates.Count131072.C028147
import PlattCertificates.Count131072.C028148
import PlattCertificates.Count131072.C028149
import PlattCertificates.Count131072.C028150
import PlattCertificates.Count131072.C028151
import PlattCertificates.Count131072.C028152
import PlattCertificates.Count131072.C028153
import PlattCertificates.Count131072.C028154
import PlattCertificates.Count131072.C028155
import PlattCertificates.Count131072.C028156
import PlattCertificates.Count131072.C028157
import PlattCertificates.Count131072.C028158
import PlattCertificates.Count131072.C028159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000254
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28128 : List PrefixCut := [⟨14,49877518,49877546⟩,
⟨127,449195719,449195969⟩,
⟨128,452169967,452170219⟩]
theorem checked28128 : checkPrefixCuts (2^48) 3690725377 9 Manual.Count131072.C028128.packed 128 cuts28128 = true := by
 decide +kernel
def pointBounds28128 : List (Nat × Nat × Nat) := [(3690739712,104406817422766,104407200283904),(3690855424,104407216740967,104407599602327)]
theorem point_links_checked28128 : (cuts28128.take 2).map (fun c => (3690725377-1+2*2^9*c.k,104406767545248+c.lower,104407150406358+c.upper)) = pointBounds28128 := by
 decide +kernel
def cuts28129 : List PrefixCut := [⟨112,396789004,396789226⟩,
⟨128,454365473,454365727⟩]
theorem checked28129 : checkPrefixCuts (2^48) 3690856449 9 Manual.Count131072.C028129.packed 128 cuts28129 = true := by
 decide +kernel
def pointBounds28129 : List (Nat × Nat × Nat) := [(3690971136,104407616504219,104407999365803)]
theorem point_links_checked28129 : (cuts28129.take 1).map (fun c => (3690856449-1+2*2^9*c.k,104407219715215+c.lower,104407602576577+c.upper)) = pointBounds28129 := by
 decide +kernel
def cuts28130 : List PrefixCut := [⟨97,337598737,337598928⟩,
⟨128,447486037,447486288⟩]
theorem checked28130 : checkPrefixCuts (2^48) 3690987521 9 Manual.Count131072.C028130.packed 128 cuts28130 = true := by
 decide +kernel
def pointBounds28130 : List (Nat × Nat × Nat) := [(3691086848,104408011679425,104408394541232)]
theorem point_links_checked28130 : (cuts28130.take 1).map (fun c => (3690987521-1+2*2^9*c.k,104407674080688+c.lower,104408056942304+c.upper)) = pointBounds28130 := by
 decide +kernel
def cuts28131 : List PrefixCut := [⟨82,287334414,287334577⟩,
⟨128,453036779,453037032⟩]
theorem checked28131 : checkPrefixCuts (2^48) 3691118593 9 Manual.Count131072.C028131.packed 128 cuts28131 = true := by
 decide +kernel
def pointBounds28131 : List (Nat × Nat × Nat) := [(3691202560,104408408901139,104408791763169)]
theorem point_links_checked28131 : (cuts28131.take 1).map (fun c => (3691118593-1+2*2^9*c.k,104408121566725+c.lower,104408504428592+c.upper)) = pointBounds28131 := by
 decide +kernel
def cuts28132 : List PrefixCut := [⟨67,241648701,241648836⟩,
⟨128,458968556,458968810⟩]
theorem checked28132 : checkPrefixCuts (2^48) 3691249665 9 Manual.Count131072.C028132.packed 128 cuts28132 = true := by
 decide +kernel
def pointBounds28132 : List (Nat × Nat × Nat) := [(3691318272,104408816252205,104409199114460)]
theorem point_links_checked28132 : (cuts28132.take 1).map (fun c => (3691249665-1+2*2^9*c.k,104408574603504+c.lower,104408957465624+c.upper)) = pointBounds28132 := by
 decide +kernel
def cuts28133 : List PrefixCut := [⟨52,187044611,187044715⟩,
⟨128,459028432,459028690⟩]
theorem checked28133 : checkPrefixCuts (2^48) 3691380737 9 Manual.Count131072.C028133.packed 128 cuts28133 = true := by
 decide +kernel
def pointBounds28133 : List (Nat × Nat × Nat) := [(3691433984,104409220616671,104409603479149)]
theorem point_links_checked28133 : (cuts28133.take 1).map (fun c => (3691380737-1+2*2^9*c.k,104409033572060+c.lower,104409416434434+c.upper)) = pointBounds28133 := by
 decide +kernel
def cuts28134 : List PrefixCut := [⟨37,135494166,135494242⟩,
⟨128,452073688,452073946⟩]
theorem checked28134 : checkPrefixCuts (2^48) 3691511809 9 Manual.Count131072.C028134.packed 128 cuts28134 = true := by
 decide +kernel
def pointBounds28134 : List (Nat × Nat × Nat) := [(3691549696,104409628094658,104410010957366)]
theorem point_links_checked28134 : (cuts28134.take 1).map (fun c => (3691511809-1+2*2^9*c.k,104409492600492+c.lower,104409875463124+c.upper)) = pointBounds28134 := by
 decide +kernel
def cuts28135 : List PrefixCut := [⟨22,77923701,77923744⟩,
⟨128,454954887,454955139⟩]
theorem checked28135 : checkPrefixCuts (2^48) 3691642881 9 Manual.Count131072.C028135.packed 128 cuts28135 = true := by
 decide +kernel
def pointBounds28135 : List (Nat × Nat × Nat) := [(3691665408,104410022597881,104410405460814)]
theorem point_links_checked28135 : (cuts28135.take 1).map (fun c => (3691642881-1+2*2^9*c.k,104409944674180+c.lower,104410327537070+c.upper)) = pointBounds28135 := by
 decide +kernel
def cuts28136 : List PrefixCut := [⟨7,26075356,26075371⟩,
⟨120,425204636,425204874⟩,
⟨128,453337634,453337888⟩]
theorem checked28136 : checkPrefixCuts (2^48) 3691773953 9 Manual.Count131072.C028136.packed 128 cuts28136 = true := by
 decide +kernel
def pointBounds28136 : List (Nat × Nat × Nat) := [(3691781120,104410425704423,104410808567580),(3691896832,104410824833703,104411207697083)]
theorem point_links_checked28136 : (cuts28136.take 2).map (fun c => (3691773953-1+2*2^9*c.k,104410399629067+c.lower,104410782492209+c.upper)) = pointBounds28136 := by
 decide +kernel
def cuts28137 : List PrefixCut := [⟨105,372279845,372280053⟩,
⟨128,454160137,454160390⟩]
theorem checked28137 : checkPrefixCuts (2^48) 3691905025 9 Manual.Count131072.C028137.packed 128 cuts28137 = true := by
 decide +kernel
def pointBounds28137 : List (Nat × Nat × Nat) := [(3692012544,104411225246546,104411608110150)]
theorem point_links_checked28137 : (cuts28137.take 1).map (fun c => (3691905025-1+2*2^9*c.k,104410852966701+c.lower,104411235830097+c.upper)) = pointBounds28137 := by
 decide +kernel
def cuts28138 : List PrefixCut := [⟨90,321874435,321874614⟩,
⟨128,455058878,455059133⟩]
theorem checked28138 : checkPrefixCuts (2^48) 3692036097 9 Manual.Count131072.C028138.packed 128 cuts28138 = true := by
 decide +kernel
def pointBounds28138 : List (Nat × Nat × Nat) := [(3692128256,104411629001273,104412011865101)]
theorem point_links_checked28138 : (cuts28138.take 1).map (fun c => (3692036097-1+2*2^9*c.k,104411307126838+c.lower,104411689990487+c.upper)) = pointBounds28138 := by
 decide +kernel
def cuts28139 : List PrefixCut := [⟨75,264916243,264916389⟩,
⟨128,453822940,453823191⟩]
theorem checked28139 : checkPrefixCuts (2^48) 3692167169 9 Manual.Count131072.C028139.packed 128 cuts28139 = true := by
 decide +kernel
def pointBounds28139 : List (Nat × Nat × Nat) := [(3692243968,104412027101959,104412409966009)]
theorem point_links_checked28139 : (cuts28139.take 1).map (fun c => (3692167169-1+2*2^9*c.k,104411762185716+c.lower,104412145049620+c.upper)) = pointBounds28139 := by
 decide +kernel
def cuts28140 : List PrefixCut := [⟨60,211011142,211011260⟩,
⟨128,459066773,459067028⟩]
theorem checked28140 : checkPrefixCuts (2^48) 3692298241 9 Manual.Count131072.C028140.packed 128 cuts28140 = true := by
 decide +kernel
def pointBounds28140 : List (Nat × Nat × Nat) := [(3692359680,104412427019798,104412809884071)]
theorem point_links_checked28140 : (cuts28140.take 1).map (fun c => (3692298241-1+2*2^9*c.k,104412216008656+c.lower,104412598872811+c.upper)) = pointBounds28140 := by
 decide +kernel
def cuts28141 : List PrefixCut := [⟨45,158329268,158329358⟩,
⟨128,448988311,448988565⟩]
theorem checked28141 : checkPrefixCuts (2^48) 3692429313 9 Manual.Count131072.C028141.packed 128 cuts28141 = true := by
 decide +kernel
def pointBounds28141 : List (Nat × Nat × Nat) := [(3692475392,104412833404697,104413216269197)]
theorem point_links_checked28141 : (cuts28141.take 1).map (fun c => (3692429313-1+2*2^9*c.k,104412675075429+c.lower,104413057939839+c.upper)) = pointBounds28141 := by
 decide +kernel
def cuts28142 : List PrefixCut := [⟨30,106870601,106870662⟩,
⟨128,456290101,456290359⟩]
theorem checked28142 : checkPrefixCuts (2^48) 3692560385 9 Manual.Count131072.C028142.packed 128 cuts28142 = true := by
 decide +kernel
def pointBounds28142 : List (Nat × Nat × Nat) := [(3692591104,104413230934341,104413613799066)]
theorem point_links_checked28142 : (cuts28142.take 1).map (fun c => (3692560385-1+2*2^9*c.k,104413124063740+c.lower,104413506928404+c.upper)) = pointBounds28142 := by
 decide +kernel
def cuts28143 : List PrefixCut := [⟨15,52213922,52213952⟩,
⟨128,453834762,453835014⟩]
theorem checked28143 : checkPrefixCuts (2^48) 3692691457 9 Manual.Count131072.C028143.packed 128 cuts28143 = true := by
 decide +kernel
def pointBounds28143 : List (Nat × Nat × Nat) := [(3692706816,104413632567763,104414015432715),(3692822528,104414034188603,104414417053777)]
theorem point_links_checked28143 : (cuts28143.take 2).map (fun c => (3692691457-1+2*2^9*c.k,104413580353841+c.lower,104413963218763+c.upper)) = pointBounds28143 := by
 decide +kernel
def cuts28144 : List PrefixCut := [⟨113,396958771,396958990⟩,
⟨128,450007622,450007870⟩]
theorem checked28144 : checkPrefixCuts (2^48) 3692822529 9 Manual.Count131072.C028144.packed 128 cuts28144 = true := by
 decide +kernel
def pointBounds28144 : List (Nat × Nat × Nat) := [(3692938240,104414431147374,104414814012767)]
theorem point_links_checked28144 : (cuts28144.take 1).map (fun c => (3692822529-1+2*2^9*c.k,104414034188603+c.lower,104414417053777+c.upper)) = pointBounds28144 := by
 decide +kernel
def cuts28145 : List PrefixCut := [⟨98,347708433,347708629⟩,
⟨128,451439852,451440106⟩]
theorem checked28145 : checkPrefixCuts (2^48) 3692953601 9 Manual.Count131072.C028145.packed 128 cuts28145 = true := by
 decide +kernel
def pointBounds28145 : List (Nat × Nat × Nat) := [(3693053952,104414831904658,104415214770276)]
theorem point_links_checked28145 : (cuts28145.take 1).map (fun c => (3692953601-1+2*2^9*c.k,104414484196225+c.lower,104414867061647+c.upper)) = pointBounds28145 := by
 decide +kernel
def cuts28146 : List PrefixCut := [⟨83,293659745,293659906⟩,
⟨128,451804867,451805117⟩]
theorem checked28146 : checkPrefixCuts (2^48) 3693084673 9 Manual.Count131072.C028146.packed 128 cuts28146 = true := by
 decide +kernel
def pointBounds28146 : List (Nat × Nat × Nat) := [(3693169664,104415229295822,104415612161659)]
theorem point_links_checked28146 : (cuts28146.take 1).map (fun c => (3693084673-1+2*2^9*c.k,104414935636077+c.lower,104415318501753+c.upper)) = pointBounds28146 := by
 decide +kernel
def cuts28147 : List PrefixCut := [⟨68,239843316,239843449⟩,
⟨128,458114405,458114657⟩]
theorem checked28147 : checkPrefixCuts (2^48) 3693215745 9 Manual.Count131072.C028147.packed 128 cuts28147 = true := by
 decide +kernel
def pointBounds28147 : List (Nat × Nat × Nat) := [(3693285376,104415627284260,104416010150319)]
theorem point_links_checked28147 : (cuts28147.take 1).map (fun c => (3693215745-1+2*2^9*c.k,104415387440944+c.lower,104415770306870+c.upper)) = pointBounds28147 := by
 decide +kernel
def cuts28148 : List PrefixCut := [⟨53,188926522,188926626⟩,
⟨128,454287768,454288023⟩]
theorem checked28148 : checkPrefixCuts (2^48) 3693346817 9 Manual.Count131072.C028148.packed 128 cuts28148 = true := by
 decide +kernel
def pointBounds28148 : List (Nat × Nat × Nat) := [(3693401088,104416034481871,104416417348153)]
theorem point_links_checked28148 : (cuts28148.take 1).map (fun c => (3693346817-1+2*2^9*c.k,104415845555349+c.lower,104416228421527+c.upper)) = pointBounds28148 := by
 decide +kernel
def cuts28149 : List PrefixCut := [⟨38,132145080,132145156⟩,
⟨128,451451919,451452173⟩]
theorem checked28149 : checkPrefixCuts (2^48) 3693477889 9 Manual.Count131072.C028149.packed 128 cuts28149 = true := by
 decide +kernel
def pointBounds28149 : List (Nat × Nat × Nat) := [(3693516800,104416431988197,104416814854706)]
theorem point_links_checked28149 : (cuts28149.take 1).map (fun c => (3693477889-1+2*2^9*c.k,104416299843117+c.lower,104416682709550+c.upper)) = pointBounds28149 := by
 decide +kernel
def cuts28150 : List PrefixCut := [⟨23,80854227,80854271⟩,
⟨128,452426529,452426781⟩]
theorem checked28150 : checkPrefixCuts (2^48) 3693608961 9 Manual.Count131072.C028150.packed 128 cuts28150 = true := by
 decide +kernel
def pointBounds28150 : List (Nat × Nat × Nat) := [(3693632512,104416832149263,104417215015994)]
theorem point_links_checked28150 : (cuts28150.take 1).map (fun c => (3693608961-1+2*2^9*c.k,104416751295036+c.lower,104417134161723+c.upper)) = pointBounds28150 := by
 decide +kernel
def cuts28151 : List PrefixCut := [⟨8,27356928,27356943⟩,
⟨121,425968793,425969032⟩,
⟨128,450962587,450962840⟩]
theorem checked28151 : checkPrefixCuts (2^48) 3693740033 9 Manual.Count131072.C028151.packed 128 cuts28151 = true := by
 decide +kernel
def pointBounds28151 : List (Nat × Nat × Nat) := [(3693748224,104417231078493,104417613945447),(3693863936,104417629690358,104418012557536)]
theorem point_links_checked28151 : (cuts28151.take 2).map (fun c => (3693740033-1+2*2^9*c.k,104417203721565+c.lower,104417586588504+c.upper)) = pointBounds28151 := by
 decide +kernel
def cuts28152 : List PrefixCut := [⟨106,378711041,378711253⟩,
⟨128,456052057,456052310⟩]
theorem checked28152 : checkPrefixCuts (2^48) 3693871105 9 Manual.Count131072.C028152.packed 128 cuts28152 = true := by
 decide +kernel
def pointBounds28152 : List (Nat × Nat × Nat) := [(3693979648,104418033395193,104418416262597)]
theorem point_links_checked28152 : (cuts28152.take 1).map (fun c => (3693871105-1+2*2^9*c.k,104417654684152+c.lower,104418037551344+c.upper)) = pointBounds28152 := by
 decide +kernel
def cuts28153 : List PrefixCut := [⟨91,320560181,320560363⟩,
⟨128,449406797,449407051⟩]
theorem checked28153 : checkPrefixCuts (2^48) 3694002177 9 Manual.Count131072.C028153.packed 128 cuts28153 = true := by
 decide +kernel
def pointBounds28153 : List (Nat × Nat × Nat) := [(3694095360,104418431296390,104418814164017)]
theorem point_links_checked28153 : (cuts28153.take 1).map (fun c => (3694002177-1+2*2^9*c.k,104418110736209+c.lower,104418493603654+c.upper)) = pointBounds28153 := by
 decide +kernel
def cuts28154 : List PrefixCut := [⟨76,266222916,266223064⟩,
⟨128,450000317,450000570⟩]
theorem checked28154 : checkPrefixCuts (2^48) 3694133249 9 Manual.Count131072.C028154.packed 128 cuts28154 = true := by
 decide +kernel
def pointBounds28154 : List (Nat × Nat × Nat) := [(3694211072,104418826365922,104419209233769)]
theorem point_links_checked28154 : (cuts28154.take 1).map (fun c => (3694133249-1+2*2^9*c.k,104418560143006+c.lower,104418943010705+c.upper)) = pointBounds28154 := by
 decide +kernel
def cuts28155 : List PrefixCut := [⟨61,212194062,212194185⟩,
⟨128,450593860,450594119⟩]
theorem checked28155 : checkPrefixCuts (2^48) 3694264321 9 Manual.Count131072.C028155.packed 128 cuts28155 = true := by
 decide +kernel
def pointBounds28155 : List (Nat × Nat × Nat) := [(3694326784,104419222337385,104419605205460)]
theorem point_links_checked28155 : (cuts28155.take 1).map (fun c => (3694264321-1+2*2^9*c.k,104419010143323+c.lower,104419393011275+c.upper)) = pointBounds28155 := by
 decide +kernel
def cuts28156 : List PrefixCut := [⟨46,161521150,161521239⟩,
⟨128,453015902,453016153⟩]
theorem checked28156 : checkPrefixCuts (2^48) 3694395393 9 Manual.Count131072.C028156.packed 128 cuts28156 = true := by
 decide +kernel
def pointBounds28156 : List (Nat × Nat × Nat) := [(3694442496,104419622258333,104420005126633)]
theorem point_links_checked28156 : (cuts28156.take 1).map (fun c => (3694395393-1+2*2^9*c.k,104419460737183+c.lower,104419843605394+c.upper)) = pointBounds28156 := by
 decide +kernel
def cuts28157 : List PrefixCut := [⟨31,115118063,115118127⟩,
⟨128,458180568,458180825⟩]
theorem checked28157 : checkPrefixCuts (2^48) 3694526465 9 Manual.Count131072.C028157.packed 128 cuts28157 = true := by
 decide +kernel
def pointBounds28157 : List (Nat × Nat × Nat) := [(3694558208,104420028871148,104420411739674)]
theorem point_links_checked28157 : (cuts28157.take 1).map (fun c => (3694526465-1+2*2^9*c.k,104419913753085+c.lower,104420296621547+c.upper)) = pointBounds28157 := by
 decide +kernel
def cuts28158 : List PrefixCut := [⟨16,56528625,56528655⟩,
⟨128,448946061,448946318⟩]
theorem checked28158 : checkPrefixCuts (2^48) 3694657537 9 Manual.Count131072.C028158.packed 128 cuts28158 = true := by
 decide +kernel
def pointBounds28158 : List (Nat × Nat × Nat) := [(3694673920,104420428462278,104420811331027)]
theorem point_links_checked28158 : (cuts28158.take 1).map (fun c => (3694657537-1+2*2^9*c.k,104420371933653+c.lower,104420754802372+c.upper)) = pointBounds28158 := by
 decide +kernel
def cuts28159 : List PrefixCut := [⟨1,3885261,3885263⟩,
⟨114,410231456,410231675⟩,
⟨128,457538641,457538889⟩]
theorem checked28159 : checkPrefixCuts (2^48) 3694788609 9 Manual.Count131072.C028159.packed 128 cuts28159 = true := by
 decide +kernel
def pointBounds28159 : List (Nat × Nat × Nat) := [(3694789632,104420824764975,104421207633953),(3694905344,104421231111170,104421613980365)]
theorem point_links_checked28159 : (cuts28159.take 2).map (fun c => (3694788609-1+2*2^9*c.k,104420820879714+c.lower,104421203748690+c.upper)) = pointBounds28159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000254
