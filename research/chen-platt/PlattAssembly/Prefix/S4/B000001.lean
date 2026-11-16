import PlattAssemblyKernel
import PlattCertificates.Count131072.C030032
import PlattCertificates.Count131072.C030033
import PlattCertificates.Count131072.C030034
import PlattCertificates.Count131072.C030035
import PlattCertificates.Count131072.C030036
import PlattCertificates.Count131072.C030037
import PlattCertificates.Count131072.C030038
import PlattCertificates.Count131072.C030039
import PlattCertificates.Count131072.C030040
import PlattCertificates.Count131072.C030041
import PlattCertificates.Count131072.C030042
import PlattCertificates.Count131072.C030043
import PlattCertificates.Count131072.C030044
import PlattCertificates.Count131072.C030045
import PlattCertificates.Count131072.C030046
import PlattCertificates.Count131072.C030047
import PlattCertificates.Count131072.C030048
import PlattCertificates.Count131072.C030049
import PlattCertificates.Count131072.C030050
import PlattCertificates.Count131072.C030051
import PlattCertificates.Count131072.C030052
import PlattCertificates.Count131072.C030053
import PlattCertificates.Count131072.C030054
import PlattCertificates.Count131072.C030055
import PlattCertificates.Count131072.C030056
import PlattCertificates.Count131072.C030057
import PlattCertificates.Count131072.C030058
import PlattCertificates.Count131072.C030059
import PlattCertificates.Count131072.C030060
import PlattCertificates.Count131072.C030061
import PlattCertificates.Count131072.C030062
import PlattCertificates.Count131072.C030063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30032 : List PrefixCut := [⟨22,73792280,73792322⟩,
⟨128,420103058,420103300⟩]
theorem checked30032 : checkPrefixCuts (2^48) 3940286465 9 Manual.Count131072.C030032.packed 128 cuts30032 = true := by
 decide +kernel
def pointBounds30032 : List (Nat × Nat × Nat) := [(3940308992,105241626383887,105242009712825)]
theorem point_links_checked30032 : (cuts30032.take 1).map (fun c => (3940286465-1+2*2^9*c.k,105241552591607+c.lower,105241935920503+c.upper)) = pointBounds30032 := by
 decide +kernel
def cuts30033 : List PrefixCut := [⟨15,50217131,50217159⟩,
⟨128,421874821,421875063⟩]
theorem checked30033 : checkPrefixCuts (2^48) 3940417537 9 Manual.Count131072.C030033.packed 128 cuts30033 = true := by
 decide +kernel
def pointBounds30033 : List (Nat × Nat × Nat) := [(3940432896,105242022911796,105242406240962)]
theorem point_links_checked30033 : (cuts30033.take 1).map (fun c => (3940417537-1+2*2^9*c.k,105241972694665+c.lower,105242356023803+c.upper)) = pointBounds30033 := by
 decide +kernel
def cuts30034 : List PrefixCut := [⟨8,26214922,26214938⟩,
⟨128,423860834,423861070⟩]
theorem checked30034 : checkPrefixCuts (2^48) 3940548609 9 Manual.Count131072.C030034.packed 128 cuts30034 = true := by
 decide +kernel
def pointBounds30034 : List (Nat × Nat × Nat) := [(3940556800,105242420784408,105242804113804)]
theorem point_links_checked30034 : (cuts30034.take 1).map (fun c => (3940548609-1+2*2^9*c.k,105242394569486+c.lower,105242777898866+c.upper)) = pointBounds30034 := by
 decide +kernel
def cuts30035 : List PrefixCut := [⟨1,3357116,3357118⟩,
⟨122,403347552,403347783⟩,
⟨128,423418169,423418412⟩]
theorem checked30035 : checkPrefixCuts (2^48) 3940679681 9 Manual.Count131072.C030035.packed 128 cuts30035 = true := by
 decide +kernel
def pointBounds30035 : List (Nat × Nat × Nat) := [(3940680704,105242821787436,105243205117054),(3940804608,105243221777872,105243605107719)]
theorem point_links_checked30035 : (cuts30035.take 2).map (fun c => (3940679681-1+2*2^9*c.k,105242818430320+c.lower,105243201759936+c.upper)) = pointBounds30035 := by
 decide +kernel
def cuts30036 : List PrefixCut := [⟨115,381835777,381835988⟩,
⟨128,425546882,425547117⟩]
theorem checked30036 : checkPrefixCuts (2^48) 3940810753 9 Manual.Count131072.C030036.packed 128 cuts30036 = true := by
 decide +kernel
def pointBounds30036 : List (Nat × Nat × Nat) := [(3940928512,105243623684266,105244007014336)]
theorem point_links_checked30036 : (cuts30036.take 1).map (fun c => (3940810753-1+2*2^9*c.k,105243241848489+c.lower,105243625178348+c.upper)) = pointBounds30036 := by
 decide +kernel
def cuts30037 : List PrefixCut := [⟨108,356611354,356611555⟩,
⟨128,423961423,423961664⟩]
theorem checked30037 : checkPrefixCuts (2^48) 3940941825 9 Manual.Count131072.C030037.packed 128 cuts30037 = true := by
 decide +kernel
def pointBounds30037 : List (Nat × Nat × Nat) := [(3941052416,105244024006725,105244407337020)]
theorem point_links_checked30037 : (cuts30037.take 1).map (fun c => (3940941825-1+2*2^9*c.k,105243667395371+c.lower,105244050725465+c.upper)) = pointBounds30037 := by
 decide +kernel
def cuts30038 : List PrefixCut := [⟨101,329603050,329603237⟩,
⟨128,416948193,416948431⟩]
theorem checked30038 : checkPrefixCuts (2^48) 3941072897 9 Manual.Count131072.C030038.packed 128 cuts30038 = true := by
 decide +kernel
def pointBounds30038 : List (Nat × Nat × Nat) := [(3941176320,105244420959844,105244804290366)]
theorem point_links_checked30038 : (cuts30038.take 1).map (fun c => (3941072897-1+2*2^9*c.k,105244091356794+c.lower,105244474687129+c.upper)) = pointBounds30038 := by
 decide +kernel
def cuts30039 : List PrefixCut := [⟨94,311809324,311809503⟩,
⟨128,423433229,423433473⟩]
theorem checked30039 : checkPrefixCuts (2^48) 3941203969 9 Manual.Count131072.C030039.packed 128 cuts30039 = true := by
 decide +kernel
def pointBounds30039 : List (Nat × Nat × Nat) := [(3941300224,105244820114311,105245203445063)]
theorem point_links_checked30039 : (cuts30039.take 1).map (fun c => (3941203969-1+2*2^9*c.k,105244508304987+c.lower,105244891635560+c.upper)) = pointBounds30039 := by
 decide +kernel
def cuts30040 : List PrefixCut := [⟨87,284732890,284733051⟩,
⟨128,421633800,421634037⟩]
theorem checked30040 : checkPrefixCuts (2^48) 3941335041 9 Manual.Count131072.C030040.packed 128 cuts30040 = true := by
 decide +kernel
def pointBounds30040 : List (Nat × Nat × Nat) := [(3941424128,105245216471106,105245599802084)]
theorem point_links_checked30040 : (cuts30040.take 1).map (fun c => (3941335041-1+2*2^9*c.k,105244931738216+c.lower,105245315069033+c.upper)) = pointBounds30040 := by
 decide +kernel
def cuts30041 : List PrefixCut := [⟨80,267084671,267084819⟩,
⟨128,423476571,423476806⟩]
theorem checked30041 : checkPrefixCuts (2^48) 3941466113 9 Manual.Count131072.C030041.packed 128 cuts30041 = true := by
 decide +kernel
def pointBounds30041 : List (Nat × Nat × Nat) := [(3941548032,105245620456687,105246003787889)]
theorem point_links_checked30041 : (cuts30041.take 1).map (fun c => (3941466113-1+2*2^9*c.k,105245353372016+c.lower,105245736703070+c.upper)) = pointBounds30041 := by
 decide +kernel
def cuts30042 : List PrefixCut := [⟨73,247009645,247009779⟩,
⟨128,432817205,432817442⟩]
theorem checked30042 : checkPrefixCuts (2^48) 3941597185 9 Manual.Count131072.C030042.packed 128 cuts30042 = true := by
 decide +kernel
def pointBounds30042 : List (Nat × Nat × Nat) := [(3941671936,105246023858232,105246407189655)]
theorem point_links_checked30042 : (cuts30042.take 1).map (fun c => (3941597185-1+2*2^9*c.k,105245776848587+c.lower,105246160179876+c.upper)) = pointBounds30042 := by
 decide +kernel
def cuts30043 : List PrefixCut := [⟨66,216510257,216510377⟩,
⟨128,422305847,422306081⟩]
theorem checked30043 : checkPrefixCuts (2^48) 3941728257 9 Manual.Count131072.C030043.packed 128 cuts30043 = true := by
 decide +kernel
def pointBounds30043 : List (Nat × Nat × Nat) := [(3941795840,105246426176049,105246809507695)]
theorem point_links_checked30043 : (cuts30043.take 1).map (fun c => (3941728257-1+2*2^9*c.k,105246209665792+c.lower,105246592997318+c.upper)) = pointBounds30043 := by
 decide +kernel
def cuts30044 : List PrefixCut := [⟨59,196937970,196938084⟩,
⟨128,423005855,423006093⟩]
theorem checked30044 : checkPrefixCuts (2^48) 3941859329 9 Manual.Count131072.C030044.packed 128 cuts30044 = true := by
 decide +kernel
def pointBounds30044 : List (Nat × Nat × Nat) := [(3941919744,105246828909609,105247212241483)]
theorem point_links_checked30044 : (cuts30044.take 1).map (fun c => (3941859329-1+2*2^9*c.k,105246631971639+c.lower,105247015303399+c.upper)) = pointBounds30044 := by
 decide +kernel
def cuts30045 : List PrefixCut := [⟨52,170869213,170869308⟩,
⟨128,424062803,424063037⟩]
theorem checked30045 : checkPrefixCuts (2^48) 3941990401 9 Manual.Count131072.C030045.packed 128 cuts30045 = true := by
 decide +kernel
def pointBounds30045 : List (Nat × Nat × Nat) := [(3942043648,105247225846707,105247609178800)]
theorem point_links_checked30045 : (cuts30045.take 1).map (fun c => (3941990401-1+2*2^9*c.k,105247054977494+c.lower,105247438309492+c.upper)) = pointBounds30045 := by
 decide +kernel
def cuts30046 : List PrefixCut := [⟨45,149157672,149157756⟩,
⟨128,421264136,421264373⟩]
theorem checked30046 : checkPrefixCuts (2^48) 3942121473 9 Manual.Count131072.C030046.packed 128 cuts30046 = true := by
 decide +kernel
def pointBounds30046 : List (Nat × Nat × Nat) := [(3942167552,105247628197969,105248011530285)]
theorem point_links_checked30046 : (cuts30046.take 1).map (fun c => (3942121473-1+2*2^9*c.k,105247479040297+c.lower,105247862372529+c.upper)) = pointBounds30046 := by
 decide +kernel
def cuts30047 : List PrefixCut := [⟨38,126019518,126019589⟩,
⟨128,424677180,424677419⟩]
theorem checked30047 : checkPrefixCuts (2^48) 3942252545 9 Manual.Count131072.C030047.packed 128 cuts30047 = true := by
 decide +kernel
def pointBounds30047 : List (Nat × Nat × Nat) := [(3942291456,105248026323951,105248409656491)]
theorem point_links_checked30047 : (cuts30047.take 1).map (fun c => (3942252545-1+2*2^9*c.k,105247900304433+c.lower,105248283636902+c.upper)) = pointBounds30047 := by
 decide +kernel
def cuts30048 : List PrefixCut := [⟨31,104168004,104168065⟩,
⟨128,425805457,425805700⟩]
theorem checked30048 : checkPrefixCuts (2^48) 3942383617 9 Manual.Count131072.C030048.packed 128 cuts30048 = true := by
 decide +kernel
def pointBounds30048 : List (Nat × Nat × Nat) := [(3942415360,105248429149617,105248812482386)]
theorem point_links_checked30048 : (cuts30048.take 1).map (fun c => (3942383617-1+2*2^9*c.k,105248324981613+c.lower,105248708314321+c.upper)) = pointBounds30048 := by
 decide +kernel
def cuts30049 : List PrefixCut := [⟨24,78391199,78391246⟩,
⟨128,421793240,421793480⟩]
theorem checked30049 : checkPrefixCuts (2^48) 3942514689 9 Manual.Count131072.C030049.packed 128 cuts30049 = true := by
 decide +kernel
def pointBounds30049 : List (Nat × Nat × Nat) := [(3942539264,105248829178269,105249212511267)]
theorem point_links_checked30049 : (cuts30049.take 1).map (fun c => (3942514689-1+2*2^9*c.k,105248750787070+c.lower,105249134120021+c.upper)) = pointBounds30049 := by
 decide +kernel
def cuts30050 : List PrefixCut := [⟨17,56685433,56685465⟩,
⟨128,426490995,426491234⟩]
theorem checked30050 : checkPrefixCuts (2^48) 3942645761 9 Manual.Count131072.C030050.packed 128 cuts30050 = true := by
 decide +kernel
def pointBounds30050 : List (Nat × Nat × Nat) := [(3942663168,105249229265743,105249612598966)]
theorem point_links_checked30050 : (cuts30050.take 1).map (fun c => (3942645761-1+2*2^9*c.k,105249172580310+c.lower,105249555913501+c.upper)) = pointBounds30050 := by
 decide +kernel
def cuts30051 : List PrefixCut := [⟨10,34766892,34766911⟩,
⟨128,423264378,423264617⟩]
theorem checked30051 : checkPrefixCuts (2^48) 3942776833 9 Manual.Count131072.C030051.packed 128 cuts30051 = true := by
 decide +kernel
def pointBounds30051 : List (Nat × Nat × Nat) := [(3942787072,105249633838197,105250017171646)]
theorem point_links_checked30051 : (cuts30051.take 1).map (fun c => (3942776833-1+2*2^9*c.k,105249599071305+c.lower,105249982404735+c.upper)) = pointBounds30051 := by
 decide +kernel
def cuts30052 : List PrefixCut := [⟨3,10137041,10137047⟩,
⟨124,409544378,409544604⟩,
⟨128,421608495,421608728⟩]
theorem checked30052 : checkPrefixCuts (2^48) 3942907905 9 Manual.Count131072.C030052.packed 128 cuts30052 = true := by
 decide +kernel
def pointBounds30052 : List (Nat × Nat × Nat) := [(3942910976,105250032472724,105250415806399),(3943034880,105250431880061,105250815213956)]
theorem point_links_checked30052 : (cuts30052.take 2).map (fun c => (3942907905-1+2*2^9*c.k,105250022335683+c.lower,105250405669352+c.upper)) = pointBounds30052 := by
 decide +kernel
def cuts30053 : List PrefixCut := [⟨117,388044441,388044660⟩,
⟨128,423735938,423736179⟩]
theorem checked30053 : checkPrefixCuts (2^48) 3943038977 9 Manual.Count131072.C030053.packed 128 cuts30053 = true := by
 decide +kernel
def pointBounds30053 : List (Nat × Nat × Nat) := [(3943158784,105250831988619,105251215322740)]
theorem point_links_checked30053 : (cuts30053.take 1).map (fun c => (3943038977-1+2*2^9*c.k,105250443944178+c.lower,105250827278080+c.upper)) = pointBounds30053 := by
 decide +kernel
def cuts30054 : List PrefixCut := [⟨110,362263036,362263241⟩,
⟨128,420081399,420081638⟩]
theorem checked30054 : checkPrefixCuts (2^48) 3943170049 9 Manual.Count131072.C030054.packed 128 cuts30054 = true := by
 decide +kernel
def pointBounds30054 : List (Nat × Nat × Nat) := [(3943282688,105251229943152,105251613277500)]
theorem point_links_checked30054 : (cuts30054.take 1).map (fun c => (3943170049-1+2*2^9*c.k,105250867680116+c.lower,105251251014259+c.upper)) = pointBounds30054 := by
 decide +kernel
def cuts30055 : List PrefixCut := [⟨103,341694007,341694199⟩,
⟨128,422066067,422066305⟩]
theorem checked30055 : checkPrefixCuts (2^48) 3943301121 9 Manual.Count131072.C030055.packed 128 cuts30055 = true := by
 decide +kernel
def pointBounds30055 : List (Nat × Nat × Nat) := [(3943406592,105251629455522,105252012790096)]
theorem point_links_checked30055 : (cuts30055.take 1).map (fun c => (3943301121-1+2*2^9*c.k,105251287761515+c.lower,105251671095897+c.upper)) = pointBounds30055 := by
 decide +kernel
def cuts30056 : List PrefixCut := [⟨96,313060659,313060831⟩,
⟨128,418126239,418126471⟩]
theorem checked30056 : checkPrefixCuts (2^48) 3943432193 9 Manual.Count131072.C030056.packed 128 cuts30056 = true := by
 decide +kernel
def pointBounds30056 : List (Nat × Nat × Nat) := [(3943530496,105252022888241,105252406223033)]
theorem point_links_checked30056 : (cuts30056.take 1).map (fun c => (3943432193-1+2*2^9*c.k,105251709827582+c.lower,105252093162202+c.upper)) = pointBounds30056 := by
 decide +kernel
def cuts30057 : List PrefixCut := [⟨89,296063331,296063501⟩,
⟨128,429175418,429175658⟩]
theorem checked30057 : checkPrefixCuts (2^48) 3943563265 9 Manual.Count131072.C030057.packed 128 cuts30057 = true := by
 decide +kernel
def pointBounds30057 : List (Nat × Nat × Nat) := [(3943654400,105252424017152,105252807352174)]
theorem point_links_checked30057 : (cuts30057.take 1).map (fun c => (3943563265-1+2*2^9*c.k,105252127953821+c.lower,105252511288673+c.upper)) = pointBounds30057 := by
 decide +kernel
def cuts30058 : List PrefixCut := [⟨82,272572137,272572289⟩,
⟨128,420810657,420810895⟩]
theorem checked30058 : checkPrefixCuts (2^48) 3943694337 9 Manual.Count131072.C030058.packed 128 cuts30058 = true := by
 decide +kernel
def pointBounds30058 : List (Nat × Nat × Nat) := [(3943778304,105252829701376,105253213036620)]
theorem point_links_checked30058 : (cuts30058.take 1).map (fun c => (3943694337-1+2*2^9*c.k,105252557129239+c.lower,105252940464331+c.upper)) = pointBounds30058 := by
 decide +kernel
def cuts30059 : List PrefixCut := [⟨75,247298224,247298359⟩,
⟨128,423294549,423294780⟩]
theorem checked30059 : checkPrefixCuts (2^48) 3943825409 9 Manual.Count131072.C030059.packed 128 cuts30059 = true := by
 decide +kernel
def pointBounds30059 : List (Nat × Nat × Nat) := [(3943902208,105253225238120,105253608573585)]
theorem point_links_checked30059 : (cuts30059.take 1).map (fun c => (3943825409-1+2*2^9*c.k,105252977939896+c.lower,105253361275226+c.upper)) = pointBounds30059 := by
 decide +kernel
def cuts30060 : List PrefixCut := [⟨68,224166992,224167120⟩,
⟨128,425350148,425350384⟩]
theorem checked30060 : checkPrefixCuts (2^48) 3943956481 9 Manual.Count131072.C030060.packed 128 cuts30060 = true := by
 decide +kernel
def pointBounds30060 : List (Nat × Nat × Nat) := [(3944026112,105253625401437,105254008737126)]
theorem point_links_checked30060 : (cuts30060.take 1).map (fun c => (3943956481-1+2*2^9*c.k,105253401234445+c.lower,105253784570006+c.upper)) = pointBounds30060 := by
 decide +kernel
def cuts30061 : List PrefixCut := [⟨61,202678661,202678771⟩,
⟨128,423837382,423837620⟩]
theorem checked30061 : checkPrefixCuts (2^48) 3944087553 9 Manual.Count131072.C030061.packed 128 cuts30061 = true := by
 decide +kernel
def pointBounds30061 : List (Nat × Nat × Nat) := [(3944150016,105254029263254,105254412599161)]
theorem point_links_checked30061 : (cuts30061.take 1).map (fun c => (3944087553-1+2*2^9*c.k,105253826584593+c.lower,105254209920390+c.upper)) = pointBounds30061 := by
 decide +kernel
def cuts30062 : List PrefixCut := [⟨54,177909011,177909111⟩,
⟨128,423537806,423538044⟩]
theorem checked30062 : checkPrefixCuts (2^48) 3944218625 9 Manual.Count131072.C030062.packed 128 cuts30062 = true := by
 decide +kernel
def pointBounds30062 : List (Nat × Nat × Nat) := [(3944273920,105254428330986,105254811667121)]
theorem point_links_checked30062 : (cuts30062.take 1).map (fun c => (3944218625-1+2*2^9*c.k,105254250421975+c.lower,105254633758010+c.upper)) = pointBounds30062 := by
 decide +kernel
def cuts30063 : List PrefixCut := [⟨47,155067702,155067790⟩,
⟨128,423381009,423381246⟩]
theorem checked30063 : checkPrefixCuts (2^48) 3944349697 9 Manual.Count131072.C030063.packed 128 cuts30063 = true := by
 decide +kernel
def pointBounds30063 : List (Nat × Nat × Nat) := [(3944397824,105254829027483,105255212363844)]
theorem point_links_checked30063 : (cuts30063.take 1).map (fun c => (3944349697-1+2*2^9*c.k,105254673959781+c.lower,105255057296054+c.upper)) = pointBounds30063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000001
