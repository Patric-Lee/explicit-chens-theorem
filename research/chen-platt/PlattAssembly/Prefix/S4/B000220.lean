import PlattAssemblyKernel
import PlattCertificates.Count131072.C037040
import PlattCertificates.Count131072.C037041
import PlattCertificates.Count131072.C037042
import PlattCertificates.Count131072.C037043
import PlattCertificates.Count131072.C037044
import PlattCertificates.Count131072.C037045
import PlattCertificates.Count131072.C037046
import PlattCertificates.Count131072.C037047
import PlattCertificates.Count131072.C037048
import PlattCertificates.Count131072.C037049
import PlattCertificates.Count131072.C037050
import PlattCertificates.Count131072.C037051
import PlattCertificates.Count131072.C037052
import PlattCertificates.Count131072.C037053
import PlattCertificates.Count131072.C037054
import PlattCertificates.Count131072.C037055
import PlattCertificates.Count131072.C037056
import PlattCertificates.Count131072.C037057
import PlattCertificates.Count131072.C037058
import PlattCertificates.Count131072.C037059
import PlattCertificates.Count131072.C037060
import PlattCertificates.Count131072.C037061
import PlattCertificates.Count131072.C037062
import PlattCertificates.Count131072.C037063
import PlattCertificates.Count131072.C037064
import PlattCertificates.Count131072.C037065
import PlattCertificates.Count131072.C037066
import PlattCertificates.Count131072.C037067
import PlattCertificates.Count131072.C037068
import PlattCertificates.Count131072.C037069
import PlattCertificates.Count131072.C037070
import PlattCertificates.Count131072.C037071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37040 : List PrefixCut := [⟨64,338541119,338541325⟩]
theorem checked37040 : checkPrefixCuts (2^48) 4858839041 10 Manual.Count131072.C037040.packed 64 cuts37040 = true := by
 decide +kernel
def cuts37041 : List PrefixCut := [⟨11,59608719,59608756⟩,
⟨64,343340084,343340291⟩]
theorem checked37041 : checkPrefixCuts (2^48) 4858970113 10 Manual.Count131072.C037041.packed 64 cuts37041 = true := by
 decide +kernel
def pointBounds37041 : List (Nat × Nat × Nat) := [(4858992640,107898829242210,107899214165828)]
theorem point_links_checked37041 : (cuts37041.take 1).map (fun c => (4858970113-1+2*2^10*c.k,107898769633491+c.lower,107899154557072+c.upper)) = pointBounds37041 := by
 decide +kernel
def cuts37042 : List PrefixCut := [⟨22,119271880,119271956⟩,
⟨64,342404028,342404233⟩]
theorem checked37042 : checkPrefixCuts (2^48) 4859101185 10 Manual.Count131072.C037042.packed 64 cuts37042 = true := by
 decide +kernel
def pointBounds37042 : List (Nat × Nat × Nat) := [(4859146240,107899232245455,107899617169319)]
theorem point_links_checked37042 : (cuts37042.take 1).map (fun c => (4859101185-1+2*2^10*c.k,107899112973575+c.lower,107899497897363+c.upper)) = pointBounds37042 := by
 decide +kernel
def cuts37043 : List PrefixCut := [⟨33,176324891,176324999⟩,
⟨64,339498528,339498734⟩]
theorem checked37043 : checkPrefixCuts (2^48) 4859232257 10 Manual.Count131072.C037043.packed 64 cuts37043 = true := by
 decide +kernel
def pointBounds37043 : List (Nat × Nat × Nat) := [(4859299840,107899631702494,107900016626595)]
theorem point_links_checked37043 : (cuts37043.take 1).map (fun c => (4859232257-1+2*2^10*c.k,107899455377603+c.lower,107899840301596+c.upper)) = pointBounds37043 := by
 decide +kernel
def cuts37044 : List PrefixCut := [⟨44,238240157,238240302⟩,
⟨64,344934168,344934377⟩]
theorem checked37044 : checkPrefixCuts (2^48) 4859363329 10 Manual.Count131072.C037044.packed 64 cuts37044 = true := by
 decide +kernel
def pointBounds37044 : List (Nat × Nat × Nat) := [(4859453440,107900033116288,107900418040632)]
theorem point_links_checked37044 : (cuts37044.take 1).map (fun c => (4859363329-1+2*2^10*c.k,107899794876131+c.lower,107900179800330+c.upper)) = pointBounds37044 := by
 decide +kernel
def cuts37045 : List PrefixCut := [⟨55,288856984,288857158⟩,
⟨64,337684572,337684775⟩]
theorem checked37045 : checkPrefixCuts (2^48) 4859494401 10 Manual.Count131072.C037045.packed 64 cuts37045 = true := by
 decide +kernel
def pointBounds37045 : List (Nat × Nat × Nat) := [(4859607040,107900428667283,107900813591865)]
theorem point_links_checked37045 : (cuts37045.take 1).map (fun c => (4859494401-1+2*2^10*c.k,107900139810299+c.lower,107900524734707+c.upper)) = pointBounds37045 := by
 decide +kernel
def cuts37046 : List PrefixCut := [⟨64,339471042,339471254⟩]
theorem checked37046 : checkPrefixCuts (2^48) 4859625473 10 Manual.Count131072.C037046.packed 64 cuts37046 = true := by
 decide +kernel
def cuts37047 : List PrefixCut := [⟨2,9904238,9904244⟩,
⟨64,338998511,338998716⟩]
theorem checked37047 : checkPrefixCuts (2^48) 4859756545 10 Manual.Count131072.C037047.packed 64 cuts37047 = true := by
 decide +kernel
def pointBounds37047 : List (Nat × Nat × Nat) := [(4859760640,107900826870151,107901211794980)]
theorem point_links_checked37047 : (cuts37047.take 1).map (fun c => (4859756545-1+2*2^10*c.k,107900816965913+c.lower,107901201890736+c.upper)) = pointBounds37047 := by
 decide +kernel
def cuts37048 : List PrefixCut := [⟨13,66605498,66605541⟩,
⟨64,343101461,343101672⟩]
theorem checked37048 : checkPrefixCuts (2^48) 4859887617 10 Manual.Count131072.C037048.packed 64 cuts37048 = true := by
 decide +kernel
def pointBounds37048 : List (Nat × Nat × Nat) := [(4859914240,107901222569922,107901607494993)]
theorem point_links_checked37048 : (cuts37048.take 1).map (fun c => (4859887617-1+2*2^10*c.k,107901155964424+c.lower,107901540889452+c.upper)) = pointBounds37048 := by
 decide +kernel
def cuts37049 : List PrefixCut := [⟨24,126952161,126952236⟩,
⟨64,341528528,341528739⟩]
theorem checked37049 : checkPrefixCuts (2^48) 4860018689 10 Manual.Count131072.C037049.packed 64 cuts37049 = true := by
 decide +kernel
def pointBounds37049 : List (Nat × Nat × Nat) := [(4860067840,107901626018046,107902010943360)]
theorem point_links_checked37049 : (cuts37049.take 1).map (fun c => (4860018689-1+2*2^10*c.k,107901499065885+c.lower,107901883991124+c.upper)) = pointBounds37049 := by
 decide +kernel
def cuts37050 : List PrefixCut := [⟨35,185210349,185210463⟩,
⟨64,339550238,339550441⟩]
theorem checked37050 : checkPrefixCuts (2^48) 4860149761 10 Manual.Count131072.C037050.packed 64 cuts37050 = true := by
 decide +kernel
def pointBounds37050 : List (Nat × Nat × Nat) := [(4860221440,107902025804762,107902410730326)]
theorem point_links_checked37050 : (cuts37050.take 1).map (fun c => (4860149761-1+2*2^10*c.k,107901840594413+c.lower,107902225519863+c.upper)) = pointBounds37050 := by
 decide +kernel
def cuts37051 : List PrefixCut := [⟨46,248271881,248272031⟩,
⟨64,345621872,345622080⟩]
theorem checked37051 : checkPrefixCuts (2^48) 4860280833 10 Manual.Count131072.C037051.packed 64 cuts37051 = true := by
 decide +kernel
def pointBounds37051 : List (Nat × Nat × Nat) := [(4860375040,107902428416532,107902813342335)]
theorem point_links_checked37051 : (cuts37051.take 1).map (fun c => (4860280833-1+2*2^10*c.k,107902180144651+c.lower,107902565070304+c.upper)) = pointBounds37051 := by
 decide +kernel
def cuts37052 : List PrefixCut := [⟨57,299979206,299979389⟩,
⟨64,336636402,336636607⟩]
theorem checked37052 : checkPrefixCuts (2^48) 4860411905 10 Manual.Count131072.C037052.packed 64 cuts37052 = true := by
 decide +kernel
def pointBounds37052 : List (Nat × Nat × Nat) := [(4860528640,107902825745729,107903210671773)]
theorem point_links_checked37052 : (cuts37052.take 1).map (fun c => (4860411905-1+2*2^10*c.k,107902525766523+c.lower,107902910692384+c.upper)) = pointBounds37052 := by
 decide +kernel
def cuts37053 : List PrefixCut := [⟨64,338075042,338075251⟩]
theorem checked37053 : checkPrefixCuts (2^48) 4860542977 10 Manual.Count131072.C037053.packed 64 cuts37053 = true := by
 decide +kernel
def cuts37054 : List PrefixCut := [⟨4,21078717,21078730⟩,
⟨64,341945753,341945961⟩]
theorem checked37054 : checkPrefixCuts (2^48) 4860674049 10 Manual.Count131072.C037054.packed 64 cuts37054 = true := by
 decide +kernel
def pointBounds37054 : List (Nat × Nat × Nat) := [(4860682240,107903221556684,107903606482972)]
theorem point_links_checked37054 : (cuts37054.take 1).map (fun c => (4860674049-1+2*2^10*c.k,107903200477967+c.lower,107903585404242+c.upper)) = pointBounds37054 := by
 decide +kernel
def cuts37055 : List PrefixCut := [⟨15,82054036,82054084⟩,
⟨64,340488882,340489087⟩]
theorem checked37055 : checkPrefixCuts (2^48) 4860805121 10 Manual.Count131072.C037055.packed 64 cuts37055 = true := by
 decide +kernel
def pointBounds37055 : List (Nat × Nat × Nat) := [(4860835840,107903624477756,107904009404287)]
theorem point_links_checked37055 : (cuts37055.take 1).map (fun c => (4860805121-1+2*2^10*c.k,107903542423720+c.lower,107903927350203+c.upper)) = pointBounds37055 := by
 decide +kernel
def cuts37056 : List PrefixCut := [⟨26,136482492,136482577⟩,
⟨64,336600077,336600281⟩]
theorem checked37056 : checkPrefixCuts (2^48) 4860936193 10 Manual.Count131072.C037056.packed 64 cuts37056 = true := by
 decide +kernel
def pointBounds37056 : List (Nat × Nat × Nat) := [(4860989440,107904019395094,107904404321867)]
theorem point_links_checked37056 : (cuts37056.take 1).map (fun c => (4860936193-1+2*2^10*c.k,107903882912602+c.lower,107904267839290+c.upper)) = pointBounds37056 := by
 decide +kernel
def cuts37057 : List PrefixCut := [⟨37,196466494,196466609⟩,
⟨64,342902407,342902609⟩]
theorem checked37057 : checkPrefixCuts (2^48) 4861067265 10 Manual.Count131072.C037057.packed 64 cuts37057 = true := by
 decide +kernel
def pointBounds37057 : List (Nat × Nat × Nat) := [(4861143040,107904415979173,107904800906180)]
theorem point_links_checked37057 : (cuts37057.take 1).map (fun c => (4861067265-1+2*2^10*c.k,107904219512679+c.lower,107904604439571+c.upper)) = pointBounds37057 := by
 decide +kernel
def cuts37058 : List PrefixCut := [⟨48,249904087,249904240⟩,
⟨64,333918442,333918645⟩]
theorem checked37058 : checkPrefixCuts (2^48) 4861198337 10 Manual.Count131072.C037058.packed 64 cuts37058 = true := by
 decide +kernel
def pointBounds37058 : List (Nat × Nat × Nat) := [(4861296640,107904812319173,107905197246420)]
theorem point_links_checked37058 : (cuts37058.take 1).map (fun c => (4861198337-1+2*2^10*c.k,107904562415086+c.lower,107904947342180+c.upper)) = pointBounds37058 := by
 decide +kernel
def cuts37059 : List PrefixCut := [⟨59,310518166,310518352⟩,
⟨64,339004625,339004828⟩]
theorem checked37059 : checkPrefixCuts (2^48) 4861329409 10 Manual.Count131072.C037059.packed 64 cuts37059 = true := by
 decide +kernel
def pointBounds37059 : List (Nat × Nat × Nat) := [(4861450240,107905206851694,107905591779177)]
theorem point_links_checked37059 : (cuts37059.take 1).map (fun c => (4861329409-1+2*2^10*c.k,107904896333528+c.lower,107905281260825+c.upper)) = pointBounds37059 := by
 decide +kernel
def cuts37060 : List PrefixCut := [⟨64,337432259,337432466⟩]
theorem checked37060 : checkPrefixCuts (2^48) 4861460481 10 Manual.Count131072.C037060.packed 64 cuts37060 = true := by
 decide +kernel
def cuts37061 : List PrefixCut := [⟨6,33638512,33638532⟩,
⟨64,340375951,340376154⟩]
theorem checked37061 : checkPrefixCuts (2^48) 4861591553 10 Manual.Count131072.C037061.packed 64 cuts37061 = true := by
 decide +kernel
def pointBounds37061 : List (Nat × Nat × Nat) := [(4861603840,107905606408924,107905991336651)]
theorem point_links_checked37061 : (cuts37061.take 1).map (fun c => (4861591553-1+2*2^10*c.k,107905572770412+c.lower,107905957698119+c.upper)) = pointBounds37061 := by
 decide +kernel
def cuts37062 : List PrefixCut := [⟨17,91301856,91301910⟩,
⟨64,334866698,334866899⟩]
theorem checked37062 : checkPrefixCuts (2^48) 4861722625 10 Manual.Count131072.C037062.packed 64 cuts37062 = true := by
 decide +kernel
def pointBounds37062 : List (Nat × Nat × Nat) := [(4861757440,107906004448219,107906389376183)]
theorem point_links_checked37062 : (cuts37062.take 1).map (fun c => (4861722625-1+2*2^10*c.k,107905913146363+c.lower,107906298074273+c.upper)) = pointBounds37062 := by
 decide +kernel
def cuts37063 : List PrefixCut := [⟨28,151798663,151798753⟩,
⟨64,345336452,345336662⟩]
theorem checked37063 : checkPrefixCuts (2^48) 4861853697 10 Manual.Count131072.C037063.packed 64 cuts37063 = true := by
 decide +kernel
def pointBounds37063 : List (Nat × Nat × Nat) := [(4861911040,107906399811724,107906784739925)]
theorem point_links_checked37063 : (cuts37063.take 1).map (fun c => (4861853697-1+2*2^10*c.k,107906248013061+c.lower,107906632941172+c.upper)) = pointBounds37063 := by
 decide +kernel
def cuts37064 : List PrefixCut := [⟨39,209049920,209050047⟩,
⟨64,341100987,341101195⟩]
theorem checked37064 : checkPrefixCuts (2^48) 4861984769 10 Manual.Count131072.C037064.packed 64 cuts37064 = true := by
 decide +kernel
def pointBounds37064 : List (Nat × Nat × Nat) := [(4862064640,107906802399433,107907187327881)]
theorem point_links_checked37064 : (cuts37064.take 1).map (fun c => (4861984769-1+2*2^10*c.k,107906593349513+c.lower,107906978277834+c.upper)) = pointBounds37064 := by
 decide +kernel
def cuts37065 : List PrefixCut := [⟨50,261898126,261898285⟩,
⟨64,335129037,335129243⟩]
theorem checked37065 : checkPrefixCuts (2^48) 4862115841 10 Manual.Count131072.C037065.packed 64 cuts37065 = true := by
 decide +kernel
def pointBounds37065 : List (Nat × Nat × Nat) := [(4862218240,107907196348626,107907581277314)]
theorem point_links_checked37065 : (cuts37065.take 1).map (fun c => (4862115841-1+2*2^10*c.k,107906934450500+c.lower,107907319379029+c.upper)) = pointBounds37065 := by
 decide +kernel
def cuts37066 : List PrefixCut := [⟨61,327884080,327884277⟩,
⟨64,343398159,343398366⟩]
theorem checked37066 : checkPrefixCuts (2^48) 4862246913 10 Manual.Count131072.C037066.packed 64 cuts37066 = true := by
 decide +kernel
def pointBounds37066 : List (Nat × Nat × Nat) := [(4862371840,107907597463617,107907982392549)]
theorem point_links_checked37066 : (cuts37066.take 1).map (fun c => (4862246913-1+2*2^10*c.k,107907269579537+c.lower,107907654508272+c.upper)) = pointBounds37066 := by
 decide +kernel
def cuts37067 : List PrefixCut := [⟨64,338179006,338179213⟩]
theorem checked37067 : checkPrefixCuts (2^48) 4862377985 10 Manual.Count131072.C037067.packed 64 cuts37067 = true := by
 decide +kernel
def cuts37068 : List PrefixCut := [⟨8,42083600,42083627⟩,
⟨64,338748769,338748977⟩]
theorem checked37068 : checkPrefixCuts (2^48) 4862509057 10 Manual.Count131072.C037068.packed 64 cuts37068 = true := by
 decide +kernel
def pointBounds37068 : List (Nat × Nat × Nat) := [(4862525440,107907993240302,107908378169478)]
theorem point_links_checked37068 : (cuts37068.take 1).map (fun c => (4862509057-1+2*2^10*c.k,107907951156702+c.lower,107908336085851+c.upper)) = pointBounds37068 := by
 decide +kernel
def cuts37069 : List PrefixCut := [⟨19,97594058,97594115⟩,
⟨64,333935196,333935395⟩]
theorem checked37069 : checkPrefixCuts (2^48) 4862640129 10 Manual.Count131072.C037069.packed 64 cuts37069 = true := by
 decide +kernel
def pointBounds37069 : List (Nat × Nat × Nat) := [(4862679040,107908387499529,107908772428943)]
theorem point_links_checked37069 : (cuts37069.take 1).map (fun c => (4862640129-1+2*2^10*c.k,107908289905471+c.lower,107908674834828+c.upper)) = pointBounds37069 := by
 decide +kernel
def cuts37070 : List PrefixCut := [⟨30,161667978,161668076⟩,
⟨64,342550766,342550972⟩]
theorem checked37070 : checkPrefixCuts (2^48) 4862771201 10 Manual.Count131072.C037070.packed 64 cuts37070 = true := by
 decide +kernel
def pointBounds37070 : List (Nat × Nat × Nat) := [(4862832640,107908785508645,107909170438299)]
theorem point_links_checked37070 : (cuts37070.take 1).map (fun c => (4862771201-1+2*2^10*c.k,107908623840667+c.lower,107909008770223+c.upper)) = pointBounds37070 := by
 decide +kernel
def cuts37071 : List PrefixCut := [⟨41,217171667,217171797⟩,
⟨64,338200420,338200622⟩]
theorem checked37071 : checkPrefixCuts (2^48) 4862902273 10 Manual.Count131072.C037071.packed 64 cuts37071 = true := by
 decide +kernel
def pointBounds37071 : List (Nat × Nat × Nat) := [(4862986240,107909183563100,107909568492992)]
theorem point_links_checked37071 : (cuts37071.take 1).map (fun c => (4862902273-1+2*2^10*c.k,107908966391433+c.lower,107909351321195+c.upper)) = pointBounds37071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000220
