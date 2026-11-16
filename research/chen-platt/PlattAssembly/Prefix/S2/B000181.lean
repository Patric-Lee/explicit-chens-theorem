import PlattAssemblyKernel
import PlattCertificates.Count131072.C015792
import PlattCertificates.Count131072.C015793
import PlattCertificates.Count131072.C015794
import PlattCertificates.Count131072.C015795
import PlattCertificates.Count131072.C015796
import PlattCertificates.Count131072.C015797
import PlattCertificates.Count131072.C015798
import PlattCertificates.Count131072.C015799
import PlattCertificates.Count131072.C015800
import PlattCertificates.Count131072.C015801
import PlattCertificates.Count131072.C015802
import PlattCertificates.Count131072.C015803
import PlattCertificates.Count131072.C015804
import PlattCertificates.Count131072.C015805
import PlattCertificates.Count131072.C015806
import PlattCertificates.Count131072.C015807
import PlattCertificates.Count131072.C015808
import PlattCertificates.Count131072.C015809
import PlattCertificates.Count131072.C015810
import PlattCertificates.Count131072.C015811
import PlattCertificates.Count131072.C015812
import PlattCertificates.Count131072.C015813
import PlattCertificates.Count131072.C015814
import PlattCertificates.Count131072.C015815
import PlattCertificates.Count131072.C015816
import PlattCertificates.Count131072.C015817
import PlattCertificates.Count131072.C015818
import PlattCertificates.Count131072.C015819
import PlattCertificates.Count131072.C015820
import PlattCertificates.Count131072.C015821
import PlattCertificates.Count131072.C015822
import PlattCertificates.Count131072.C015823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15792 : List PrefixCut := [⟨38,244714690,244714852⟩,
⟨102,660434171,660434601⟩,
⟨128,831712742,831713282⟩]
theorem checked15792 : checkPrefixCuts (2^48) 2073821185 9 Manual.Count131072.C015792.packed 128 cuts15792 = true := by
 decide +kernel
def pointBounds15792 : List (Nat × Nat × Nat) := [(2073860096,96943640934626,96944019411997),(2073925632,96944056654107,96944435131746)]
theorem point_links_checked15792 : (cuts15792.take 2).map (fun c => (2073821185-1+2*2^9*c.k,96943396219936+c.lower,96943774697145+c.upper)) = pointBounds15792 := by
 decide +kernel
def cuts15793 : List PrefixCut := [⟨38,252163660,252163822⟩,
⟨102,664735428,664735865⟩,
⟨128,831117564,831118109⟩]
theorem checked15793 : checkPrefixCuts (2^48) 2073952257 9 Manual.Count131072.C015793.packed 128 cuts15793 = true := by
 decide +kernel
def pointBounds15793 : List (Nat × Nat × Nat) := [(2073991168,96944480096338,96944858574249),(2074056704,96944892668106,96945271146292)]
theorem point_links_checked15793 : (cuts15793.take 2).map (fun c => (2073952257-1+2*2^9*c.k,96944227932678+c.lower,96944606410427+c.upper)) = pointBounds15793 := by
 decide +kernel
def cuts15794 : List PrefixCut := [⟨38,247397938,247398096⟩,
⟨102,658315144,658315568⟩,
⟨128,824008263,824008797⟩]
theorem checked15794 : checkPrefixCuts (2^48) 2074083329 9 Manual.Count131072.C015794.packed 128 cuts15794 = true := by
 decide +kernel
def pointBounds15794 : List (Nat × Nat × Nat) := [(2074122240,96945306448180,96945684926632),(2074187776,96945717365386,96946095844104)]
theorem point_links_checked15794 : (cuts15794.take 2).map (fun c => (2074083329-1+2*2^9*c.k,96945059050242+c.lower,96945437528536+c.upper)) = pointBounds15794 := by
 decide +kernel
def cuts15795 : List PrefixCut := [⟨38,246568121,246568279⟩,
⟨102,655695224,655695645⟩,
⟨128,825313003,825313536⟩]
theorem checked15795 : checkPrefixCuts (2^48) 2074214401 9 Manual.Count131072.C015795.packed 128 cuts15795 = true := by
 decide +kernel
def pointBounds15795 : List (Nat × Nat × Nat) := [(2074253312,96946129626626,96946508105612),(2074318848,96946538753729,96946917232978)]
theorem point_links_checked15795 : (cuts15795.take 2).map (fun c => (2074214401-1+2*2^9*c.k,96945883058505+c.lower,96946261537333+c.upper)) = pointBounds15795 := by
 decide +kernel
def cuts15796 : List PrefixCut := [⟨38,243295886,243296048⟩,
⟨102,661081315,661081744⟩,
⟨128,831366814,831367353⟩]
theorem checked15796 : checkPrefixCuts (2^48) 2074345473 9 Manual.Count131072.C015796.packed 128 cuts15796 = true := by
 decide +kernel
def pointBounds15796 : List (Nat × Nat × Nat) := [(2074384384,96946951667394,96947330146917),(2074449920,96947369452823,96947747932613)]
theorem point_links_checked15796 : (cuts15796.take 2).map (fun c => (2074345473-1+2*2^9*c.k,96946708371508+c.lower,96947086850869+c.upper)) = pointBounds15796 := by
 decide +kernel
def cuts15797 : List PrefixCut := [⟨38,243823269,243823424⟩,
⟨102,659275755,659276178⟩,
⟨128,828600736,828601266⟩]
theorem checked15797 : checkPrefixCuts (2^48) 2074476545 9 Manual.Count131072.C015797.packed 128 cuts15797 = true := by
 decide +kernel
def pointBounds15797 : List (Nat × Nat × Nat) := [(2074515456,96947783561591,96948162041646),(2074580992,96948199014077,96948577494400)]
theorem point_links_checked15797 : (cuts15797.take 2).map (fun c => (2074476545-1+2*2^9*c.k,96947539738322+c.lower,96947918218222+c.upper)) = pointBounds15797 := by
 decide +kernel
def cuts15798 : List PrefixCut := [⟨38,249370555,249370712⟩,
⟨102,667510118,667510548⟩,
⟨128,835196359,835196899⟩]
theorem checked15798 : checkPrefixCuts (2^48) 2074607617 9 Manual.Count131072.C015798.packed 128 cuts15798 = true := by
 decide +kernel
def pointBounds15798 : List (Nat × Nat × Nat) := [(2074646528,96948617709613,96948996190200),(2074712064,96949035849176,96949414330036)]
theorem point_links_checked15798 : (cuts15798.take 2).map (fun c => (2074607617-1+2*2^9*c.k,96948368339058+c.lower,96948746819488+c.upper)) = pointBounds15798 := by
 decide +kernel
def cuts15799 : List PrefixCut := [⟨38,244470776,244470935⟩,
⟨102,658920999,658921426⟩,
⟨128,832294387,832294924⟩]
theorem checked15799 : checkPrefixCuts (2^48) 2074738689 9 Manual.Count131072.C015799.packed 128 cuts15799 = true := by
 decide +kernel
def pointBounds15799 : List (Nat × Nat × Nat) := [(2074777600,96949448006193,96949826487322),(2074843136,96949862456416,96950240937813)]
theorem point_links_checked15799 : (cuts15799.take 2).map (fun c => (2074738689-1+2*2^9*c.k,96949203535417+c.lower,96949582016387+c.upper)) = pointBounds15799 := by
 decide +kernel
def cuts15800 : List PrefixCut := [⟨38,252730456,252730616⟩,
⟨102,671224190,671224623⟩,
⟨128,832920620,832921156⟩]
theorem checked15800 : checkPrefixCuts (2^48) 2074869761 9 Manual.Count131072.C015800.packed 128 cuts15800 = true := by
 decide +kernel
def pointBounds15800 : List (Nat × Nat × Nat) := [(2074908672,96950288560260,96950667041927),(2074974208,96950707053994,96951085535934)]
theorem point_links_checked15800 : (cuts15800.take 2).map (fun c => (2074869761-1+2*2^9*c.k,96950035829804+c.lower,96950414311311+c.upper)) = pointBounds15800 := by
 decide +kernel
def cuts15801 : List PrefixCut := [⟨38,247695466,247695627⟩,
⟨102,659651738,659652166⟩,
⟨128,828255732,828256269⟩]
theorem checked15801 : checkPrefixCuts (2^48) 2075000833 9 Manual.Count131072.C015801.packed 128 cuts15801 = true := by
 decide +kernel
def pointBounds15801 : List (Nat × Nat × Nat) := [(2075039744,96951116445890,96951494928094),(2075105280,96951528402162,96951906884633)]
theorem point_links_checked15801 : (cuts15801.take 2).map (fun c => (2075000833-1+2*2^9*c.k,96950868750424+c.lower,96951247232467+c.upper)) = pointBounds15801 := by
 decide +kernel
def cuts15802 : List PrefixCut := [⟨38,247544175,247544334⟩,
⟨102,659745724,659746154⟩,
⟨128,838511647,838512193⟩]
theorem checked15802 : checkPrefixCuts (2^48) 2075131905 9 Manual.Count131072.C015802.packed 128 cuts15802 = true := by
 decide +kernel
def pointBounds15802 : List (Nat × Nat × Nat) := [(2075170816,96951944550331,96952323033070),(2075236352,96952356751880,96952735234890)]
theorem point_links_checked15802 : (cuts15802.take 2).map (fun c => (2075131905-1+2*2^9*c.k,96951697006156+c.lower,96952075488736+c.upper)) = pointBounds15802 := by
 decide +kernel
def cuts15803 : List PrefixCut := [⟨38,247935436,247935602⟩,
⟨102,672317600,672318033⟩,
⟨128,842663436,842663977⟩]
theorem checked15803 : checkPrefixCuts (2^48) 2075262977 9 Manual.Count131072.C015803.packed 128 cuts15803 = true := by
 decide +kernel
def pointBounds15803 : List (Nat × Nat × Nat) := [(2075301888,96952783453239,96953161936531),(2075367424,96953207835403,96953586318962)]
theorem point_links_checked15803 : (cuts15803.take 2).map (fun c => (2075262977-1+2*2^9*c.k,96952535517803+c.lower,96952914000929+c.upper)) = pointBounds15803 := by
 decide +kernel
def cuts15804 : List PrefixCut := [⟨38,241681112,241681275⟩,
⟨102,650847047,650847473⟩,
⟨128,814672508,814673042⟩]
theorem checked15804 : checkPrefixCuts (2^48) 2075394049 9 Manual.Count131072.C015804.packed 128 cuts15804 = true := by
 decide +kernel
def pointBounds15804 : List (Nat × Nat × Nat) := [(2075432960,96953619862351,96953998346181),(2075498496,96954029028286,96954407512379)]
theorem point_links_checked15804 : (cuts15804.take 2).map (fun c => (2075394049-1+2*2^9*c.k,96953378181239+c.lower,96953756664906+c.upper)) = pointBounds15804 := by
 decide +kernel
def cuts15805 : List PrefixCut := [⟨38,240445335,240445494⟩,
⟨102,651348402,651348821⟩,
⟨128,817333230,817333757⟩]
theorem checked15805 : checkPrefixCuts (2^48) 2075525121 9 Manual.Count131072.C015805.packed 128 cuts15805 = true := by
 decide +kernel
def pointBounds15805 : List (Nat × Nat × Nat) := [(2075564032,96954433299082,96954811783442),(2075629568,96954844202149,96955222686769)]
theorem point_links_checked15805 : (cuts15805.take 2).map (fun c => (2075525121-1+2*2^9*c.k,96954192853747+c.lower,96954571337948+c.upper)) = pointBounds15805 := by
 decide +kernel
def cuts15806 : List PrefixCut := [⟨38,243006677,243006833⟩,
⟨102,654154945,654155368⟩,
⟨128,828536530,828537064⟩]
theorem checked15806 : checkPrefixCuts (2^48) 2075656193 9 Manual.Count131072.C015806.packed 128 cuts15806 = true := by
 decide +kernel
def pointBounds15806 : List (Nat × Nat × Nat) := [(2075695104,96955253193654,96955631678538),(2075760640,96955664341922,96956042827073)]
theorem point_links_checked15806 : (cuts15806.take 2).map (fun c => (2075656193-1+2*2^9*c.k,96955010186977+c.lower,96955388671705+c.upper)) = pointBounds15806 := by
 decide +kernel
def cuts15807 : List PrefixCut := [⟨38,246652441,246652601⟩,
⟨102,664418937,664419367⟩,
⟨128,836755609,836756152⟩]
theorem checked15807 : checkPrefixCuts (2^48) 2075787265 9 Manual.Count131072.C015807.packed 128 cuts15807 = true := by
 decide +kernel
def pointBounds15807 : List (Nat × Nat × Nat) := [(2075826176,96956085375948,96956463861370),(2075891712,96956503142444,96956881628136)]
theorem point_links_checked15807 : (cuts15807.take 2).map (fun c => (2075787265-1+2*2^9*c.k,96955838723507+c.lower,96956217208769+c.upper)) = pointBounds15807 := by
 decide +kernel
def cuts15808 : List PrefixCut := [⟨38,245823334,245823495⟩,
⟨102,656648529,656648958⟩,
⟨128,821381666,821382203⟩]
theorem checked15808 : checkPrefixCuts (2^48) 2075918337 9 Manual.Count131072.C015808.packed 128 cuts15808 = true := by
 decide +kernel
def pointBounds15808 : List (Nat × Nat × Nat) := [(2075957248,96956921302450,96957299788416),(2076022784,96957332127645,96957710613879)]
theorem point_links_checked15808 : (cuts15808.take 2).map (fun c => (2075918337-1+2*2^9*c.k,96956675479116+c.lower,96957053964921+c.upper)) = pointBounds15808 := by
 decide +kernel
def cuts15809 : List PrefixCut := [⟨38,251502224,251502388⟩,
⟨102,667453349,667453784⟩,
⟨128,833260693,833261234⟩]
theorem checked15809 : checkPrefixCuts (2^48) 2076049409 9 Manual.Count131072.C015809.packed 128 cuts15809 = true := by
 decide +kernel
def pointBounds15809 : List (Nat × Nat × Nat) := [(2076088320,96957748363006,96958126849512),(2076153856,96958164314131,96958542800908)]
theorem point_links_checked15809 : (cuts15809.take 2).map (fun c => (2076049409-1+2*2^9*c.k,96957496860782+c.lower,96957875347124+c.upper)) = pointBounds15809 := by
 decide +kernel
def cuts15810 : List PrefixCut := [⟨38,239284819,239284975⟩,
⟨102,655345286,655345707⟩,
⟨128,823446787,823447319⟩]
theorem checked15810 : checkPrefixCuts (2^48) 2076180481 9 Manual.Count131072.C015810.packed 128 cuts15810 = true := by
 decide +kernel
def pointBounds15810 : List (Nat × Nat × Nat) := [(2076219392,96958569406294,96958947893333),(2076284928,96958985466761,96959363954065)]
theorem point_links_checked15810 : (cuts15810.take 2).map (fun c => (2076180481-1+2*2^9*c.k,96958330121475+c.lower,96958708608358+c.upper)) = pointBounds15810 := by
 decide +kernel
def cuts15811 : List PrefixCut := [⟨38,244556716,244556874⟩,
⟨102,658557478,658557906⟩,
⟨128,826106132,826106668⟩]
theorem checked15811 : checkPrefixCuts (2^48) 2076311553 9 Manual.Count131072.C015811.packed 128 cuts15811 = true := by
 decide +kernel
def pointBounds15811 : List (Nat × Nat × Nat) := [(2076350464,96959398124978,96959776612551),(2076416000,96959812125740,96960190613583)]
theorem point_links_checked15811 : (cuts15811.take 2).map (fun c => (2076311553-1+2*2^9*c.k,96959153568262+c.lower,96959532055677+c.upper)) = pointBounds15811 := by
 decide +kernel
def cuts15812 : List PrefixCut := [⟨38,241423518,241423676⟩,
⟨102,660278014,660278439⟩,
⟨128,832424752,832425291⟩]
theorem checked15812 : checkPrefixCuts (2^48) 2076442625 9 Manual.Count131072.C015812.packed 128 cuts15812 = true := by
 decide +kernel
def pointBounds15812 : List (Nat × Nat × Nat) := [(2076481536,96960221097912,96960599586021),(2076547072,96960639952408,96961018440784)]
theorem point_links_checked15812 : (cuts15812.take 2).map (fun c => (2076442625-1+2*2^9*c.k,96959979674394+c.lower,96960358162345+c.upper)) = pointBounds15812 := by
 decide +kernel
def cuts15813 : List PrefixCut := [⟨38,241950460,241950619⟩,
⟨102,655221292,655221717⟩,
⟨128,816649500,816650029⟩]
theorem checked15813 : checkPrefixCuts (2^48) 2076573697 9 Manual.Count131072.C015813.packed 128 cuts15813 = true := by
 decide +kernel
def pointBounds15813 : List (Nat × Nat × Nat) := [(2076612608,96961054049606,96961432538255),(2076678144,96961467320438,96961845809353)]
theorem point_links_checked15813 : (cuts15813.take 2).map (fun c => (2076573697-1+2*2^9*c.k,96960812099146+c.lower,96961190587636+c.upper)) = pointBounds15813 := by
 decide +kernel
def cuts15814 : List PrefixCut := [⟨38,239088878,239089037⟩,
⟨102,653417900,653418323⟩,
⟨128,819986118,819986649⟩]
theorem checked15814 : checkPrefixCuts (2^48) 2076704769 9 Manual.Count131072.C015814.packed 128 cuts15814 = true := by
 decide +kernel
def pointBounds15814 : List (Nat × Nat × Nat) := [(2076743680,96961867837524,96962246326702),(2076809216,96962282166546,96962660655988)]
theorem point_links_checked15814 : (cuts15814.take 2).map (fun c => (2076704769-1+2*2^9*c.k,96961628748646+c.lower,96962007237665+c.upper)) = pointBounds15814 := by
 decide +kernel
def cuts15815 : List PrefixCut := [⟨38,241242315,241242473⟩,
⟨102,659610962,659611387⟩,
⟨128,829556745,829557280⟩]
theorem checked15815 : checkPrefixCuts (2^48) 2076835841 9 Manual.Count131072.C015815.packed 128 cuts15815 = true := by
 decide +kernel
def pointBounds15815 : List (Nat × Nat × Nat) := [(2076874752,96962689977079,96963068466787),(2076940288,96963108345726,96963486835701)]
theorem point_links_checked15815 : (cuts15815.take 2).map (fun c => (2076835841-1+2*2^9*c.k,96962448734764+c.lower,96962827224314+c.upper)) = pointBounds15815 := by
 decide +kernel
def cuts15816 : List PrefixCut := [⟨38,243801917,243802076⟩,
⟨102,653471050,653471478⟩,
⟨128,821508935,821509472⟩]
theorem checked15816 : checkPrefixCuts (2^48) 2076966913 9 Manual.Count131072.C015816.packed 128 cuts15816 = true := by
 decide +kernel
def pointBounds15816 : List (Nat × Nat × Nat) := [(2077005824,96963522093426,96963900583670),(2077071360,96963931762559,96964310253072)]
theorem point_links_checked15816 : (cuts15816.take 2).map (fun c => (2076966913-1+2*2^9*c.k,96963278291509+c.lower,96963656781594+c.upper)) = pointBounds15816 := by
 decide +kernel
def cuts15817 : List PrefixCut := [⟨38,247038823,247038981⟩,
⟨102,653836404,653836824⟩,
⟨128,822676704,822677235⟩]
theorem checked15817 : checkPrefixCuts (2^48) 2077097985 9 Manual.Count131072.C015817.packed 128 cuts15817 = true := by
 decide +kernel
def pointBounds15817 : List (Nat × Nat × Nat) := [(2077136896,96964346839267,96964725330047),(2077202432,96964753636848,96965132127890)]
theorem point_links_checked15817 : (cuts15817.take 2).map (fun c => (2077097985-1+2*2^9*c.k,96964099800444+c.lower,96964478291066+c.upper)) = pointBounds15817 := by
 decide +kernel
def cuts15818 : List PrefixCut := [⟨38,246616764,246616928⟩,
⟨102,664228706,664229141⟩,
⟨128,829806409,829806952⟩]
theorem checked15818 : checkPrefixCuts (2^48) 2077229057 9 Manual.Count131072.C015818.packed 128 cuts15818 = true := by
 decide +kernel
def pointBounds15818 : List (Nat × Nat × Nat) := [(2077267968,96965169093912,96965547585229),(2077333504,96965586705854,96965965197442)]
theorem point_links_checked15818 : (cuts15818.take 2).map (fun c => (2077229057-1+2*2^9*c.k,96964922477148+c.lower,96965300968301+c.upper)) = pointBounds15818 := by
 decide +kernel
def cuts15819 : List PrefixCut := [⟨38,242536380,242536541⟩,
⟨102,650231056,650231483⟩,
⟨128,814714383,814714919⟩]
theorem checked15819 : checkPrefixCuts (2^48) 2077360129 9 Manual.Count131072.C015819.packed 128 cuts15819 = true := by
 decide +kernel
def pointBounds15819 : List (Nat × Nat × Nat) := [(2077399040,96965994819937,96966373311794),(2077464576,96966402514613,96966781006736)]
theorem point_links_checked15819 : (cuts15819.take 2).map (fun c => (2077360129-1+2*2^9*c.k,96965752283557+c.lower,96966130775253+c.upper)) = pointBounds15819 := by
 decide +kernel
def cuts15820 : List PrefixCut := [⟨38,248346930,248347093⟩,
⟨102,657912671,657913105⟩,
⟨128,826450066,826450608⟩]
theorem checked15820 : checkPrefixCuts (2^48) 2077491201 9 Manual.Count131072.C015820.packed 128 cuts15820 = true := by
 decide +kernel
def pointBounds15820 : List (Nat × Nat × Nat) := [(2077530112,96966815344870,96967193837265),(2077595648,96967224910611,96967603403277)]
theorem point_links_checked15820 : (cuts15820.take 2).map (fun c => (2077491201-1+2*2^9*c.k,96966566997940+c.lower,96966945490172+c.upper)) = pointBounds15820 := by
 decide +kernel
def cuts15821 : List PrefixCut := [⟨38,248602262,248602425⟩,
⟨102,658684079,658684514⟩,
⟨128,826668933,826669477⟩]
theorem checked15821 : checkPrefixCuts (2^48) 2077622273 9 Manual.Count131072.C015821.packed 128 cuts15821 = true := by
 decide +kernel
def pointBounds15821 : List (Nat × Nat × Nat) := [(2077661184,96967642050268,96968020543205),(2077726720,96968052132085,96968430625294)]
theorem point_links_checked15821 : (cuts15821.take 2).map (fun c => (2077622273-1+2*2^9*c.k,96967393448006+c.lower,96967771940780+c.upper)) = pointBounds15821 := by
 decide +kernel
def cuts15822 : List PrefixCut := [⟨38,248044717,248044874⟩,
⟨102,664332105,664332528⟩,
⟨128,828513386,828513918⟩]
theorem checked15822 : checkPrefixCuts (2^48) 2077753345 9 Manual.Count131072.C015822.packed 128 cuts15822 = true := by
 decide +kernel
def pointBounds15822 : List (Nat × Nat × Nat) := [(2077792256,96968468161656,96968846655131),(2077857792,96968884449044,96969262942785)]
theorem point_links_checked15822 : (cuts15822.take 2).map (fun c => (2077753345-1+2*2^9*c.k,96968220116939+c.lower,96968598610257+c.upper)) = pointBounds15822 := by
 decide +kernel
def cuts15823 : List PrefixCut := [⟨38,247893558,247893721⟩,
⟨102,662393766,662394201⟩,
⟨128,829544717,829545258⟩]
theorem checked15823 : checkPrefixCuts (2^48) 2077884417 9 Manual.Count131072.C015823.packed 128 cuts15823 = true := by
 decide +kernel
def pointBounds15823 : List (Nat × Nat × Nat) := [(2077923328,96969296523883,96969675017896),(2077988864,96969711024091,96970089518376)]
theorem point_links_checked15823 : (cuts15823.take 2).map (fun c => (2077884417-1+2*2^9*c.k,96969048630325+c.lower,96969427124175+c.upper)) = pointBounds15823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000181
