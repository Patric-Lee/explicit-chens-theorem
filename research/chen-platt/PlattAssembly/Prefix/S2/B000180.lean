import PlattAssemblyKernel
import PlattCertificates.Count131072.C015760
import PlattCertificates.Count131072.C015761
import PlattCertificates.Count131072.C015762
import PlattCertificates.Count131072.C015763
import PlattCertificates.Count131072.C015764
import PlattCertificates.Count131072.C015765
import PlattCertificates.Count131072.C015766
import PlattCertificates.Count131072.C015767
import PlattCertificates.Count131072.C015768
import PlattCertificates.Count131072.C015769
import PlattCertificates.Count131072.C015770
import PlattCertificates.Count131072.C015771
import PlattCertificates.Count131072.C015772
import PlattCertificates.Count131072.C015773
import PlattCertificates.Count131072.C015774
import PlattCertificates.Count131072.C015775
import PlattCertificates.Count131072.C015776
import PlattCertificates.Count131072.C015777
import PlattCertificates.Count131072.C015778
import PlattCertificates.Count131072.C015779
import PlattCertificates.Count131072.C015780
import PlattCertificates.Count131072.C015781
import PlattCertificates.Count131072.C015782
import PlattCertificates.Count131072.C015783
import PlattCertificates.Count131072.C015784
import PlattCertificates.Count131072.C015785
import PlattCertificates.Count131072.C015786
import PlattCertificates.Count131072.C015787
import PlattCertificates.Count131072.C015788
import PlattCertificates.Count131072.C015789
import PlattCertificates.Count131072.C015790
import PlattCertificates.Count131072.C015791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15760 : List PrefixCut := [⟨38,241810560,241810714⟩,
⟨102,661908333,661908757⟩,
⟨128,830814108,830814644⟩]
theorem checked15760 : checkPrefixCuts (2^48) 2069626881 9 Manual.Count131072.C015760.packed 128 cuts15760 = true := by
 decide +kernel
def pointBounds15760 : List (Nat × Nat × Nat) := [(2069665792,96917076833175,96917455293326),(2069731328,96917496930948,96917875391369)]
theorem point_links_checked15760 : (cuts15760.take 2).map (fun c => (2069626881-1+2*2^9*c.k,96916835022615+c.lower,96917213482612+c.upper)) = pointBounds15760 := by
 decide +kernel
def cuts15761 : List PrefixCut := [⟨38,243019165,243019328⟩,
⟨102,658738761,658739192⟩,
⟨128,829537630,829538169⟩]
theorem checked15761 : checkPrefixCuts (2^48) 2069757953 9 Manual.Count131072.C015761.packed 128 cuts15761 = true := by
 decide +kernel
def pointBounds15761 : List (Nat × Nat × Nat) := [(2069796864,96917908855888,96918287316584),(2069862400,96918324575484,96918703036448)]
theorem point_links_checked15761 : (cuts15761.take 2).map (fun c => (2069757953-1+2*2^9*c.k,96917665836723+c.lower,96918044297256+c.upper)) = pointBounds15761 := by
 decide +kernel
def cuts15762 : List PrefixCut := [⟨38,251842778,251842941⟩,
⟨102,673519105,673519540⟩,
⟨128,839140009,839140550⟩]
theorem checked15762 : checkPrefixCuts (2^48) 2069889025 9 Manual.Count131072.C015762.packed 128 cuts15762 = true := by
 decide +kernel
def pointBounds15762 : List (Nat × Nat × Nat) := [(2069927936,96918747217131,96919125678366),(2069993472,96919168893458,96919547354965)]
theorem point_links_checked15762 : (cuts15762.take 2).map (fun c => (2069889025-1+2*2^9*c.k,96918495374353+c.lower,96918873835425+c.upper)) = pointBounds15762 := by
 decide +kernel
def cuts15763 : List PrefixCut := [⟨38,246251809,246251967⟩,
⟨102,651176917,651177341⟩,
⟨128,819234785,819235317⟩]
theorem checked15763 : checkPrefixCuts (2^48) 2070020097 9 Manual.Count131072.C015763.packed 128 cuts15763 = true := by
 decide +kernel
def pointBounds15763 : List (Nat × Nat × Nat) := [(2070059008,96919580766171,96919959227942),(2070124544,96919985691279,96920364153316)]
theorem point_links_checked15763 : (cuts15763.take 2).map (fun c => (2070020097-1+2*2^9*c.k,96919334514362+c.lower,96919712975975+c.upper)) = pointBounds15763 := by
 decide +kernel
def cuts15764 : List PrefixCut := [⟨38,242973049,242973208⟩,
⟨102,655214591,655215018⟩,
⟨128,826388911,826389449⟩]
theorem checked15764 : checkPrefixCuts (2^48) 2070151169 9 Manual.Count131072.C015764.packed 128 cuts15764 = true := by
 decide +kernel
def pointBounds15764 : List (Nat × Nat × Nat) := [(2070190080,96920396722196,96920775184500),(2070255616,96920808963738,96921187426310)]
theorem point_links_checked15764 : (cuts15764.take 2).map (fun c => (2070151169-1+2*2^9*c.k,96920153749147+c.lower,96920532211292+c.upper)) = pointBounds15764 := by
 decide +kernel
def cuts15765 : List PrefixCut := [⟨38,248939792,248939951⟩,
⟨102,665233902,665234330⟩,
⟨128,836261442,836261979⟩]
theorem checked15765 : checkPrefixCuts (2^48) 2070282241 9 Manual.Count131072.C015765.packed 128 cuts15765 = true := by
 decide +kernel
def pointBounds15765 : List (Nat × Nat × Nat) := [(2070321152,96921229077850,96921607540692),(2070386688,96921645371960,96922023835071)]
theorem point_links_checked15765 : (cuts15765.take 2).map (fun c => (2070282241-1+2*2^9*c.k,96920980138058+c.lower,96921358600741+c.upper)) = pointBounds15765 := by
 decide +kernel
def cuts15766 : List PrefixCut := [⟨38,252458740,252458906⟩,
⟨102,666279342,666279783⟩,
⟨128,836616325,836616873⟩]
theorem checked15766 : checkPrefixCuts (2^48) 2070413313 9 Manual.Count131072.C015766.packed 128 cuts15766 = true := by
 decide +kernel
def pointBounds15766 : List (Nat × Nat × Nat) := [(2070452224,96922068858240,96922447321626),(2070517760,96922482678842,96922861142503)]
theorem point_links_checked15766 : (cuts15766.take 2).map (fun c => (2070413313-1+2*2^9*c.k,96921816399500+c.lower,96922194862720+c.upper)) = pointBounds15766 := by
 decide +kernel
def cuts15767 : List PrefixCut := [⟨38,245509792,245509953⟩,
⟨102,664741853,664742284⟩,
⟨128,837378942,837379483⟩]
theorem checked15767 : checkPrefixCuts (2^48) 2070544385 9 Manual.Count131072.C015767.packed 128 cuts15767 = true := by
 decide +kernel
def pointBounds15767 : List (Nat × Nat × Nat) := [(2070583296,96922898525617,96923276989546),(2070648832,96923317757678,96923696221877)]
theorem point_links_checked15767 : (cuts15767.take 2).map (fun c => (2070544385-1+2*2^9*c.k,96922653015825+c.lower,96923031479593+c.upper)) = pointBounds15767 := by
 decide +kernel
def cuts15768 : List PrefixCut := [⟨38,242095898,242096054⟩,
⟨102,653961233,653961651⟩,
⟨128,824140757,824141288⟩]
theorem checked15768 : checkPrefixCuts (2^48) 2070675457 9 Manual.Count131072.C015768.packed 128 cuts15768 = true := by
 decide +kernel
def pointBounds15768 : List (Nat × Nat × Nat) := [(2070714368,96923732490665,96924110955130),(2070779904,96924144356000,96924522820727)]
theorem point_links_checked15768 : (cuts15768.take 2).map (fun c => (2070675457-1+2*2^9*c.k,96923490394767+c.lower,96923868859076+c.upper)) = pointBounds15768 := by
 decide +kernel
def cuts15769 : List PrefixCut := [⟨38,245750546,245750705⟩,
⟨102,656774236,656774662⟩,
⟨128,831700092,831700632⟩]
theorem checked15769 : checkPrefixCuts (2^48) 2070806529 9 Manual.Count131072.C015769.packed 128 cuts15769 = true := by
 decide +kernel
def pointBounds15769 : List (Nat × Nat × Nat) := [(2070845440,96924560286070,96924938751069),(2070910976,96924971309760,96925349775026)]
theorem point_links_checked15769 : (cuts15769.take 2).map (fun c => (2070806529-1+2*2^9*c.k,96924314535524+c.lower,96924693000364+c.upper)) = pointBounds15769 := by
 decide +kernel
def cuts15770 : List PrefixCut := [⟨38,241521601,241521759⟩,
⟨102,655781120,655781546⟩,
⟨128,826346797,826347335⟩]
theorem checked15770 : checkPrefixCuts (2^48) 2070937601 9 Manual.Count131072.C015770.packed 128 cuts15770 = true := by
 decide +kernel
def pointBounds15770 : List (Nat × Nat × Nat) := [(2070976512,96925387757217,96925766222755),(2071042048,96925802016736,96926180482542)]
theorem point_links_checked15770 : (cuts15770.take 2).map (fun c => (2070937601-1+2*2^9*c.k,96925146235616+c.lower,96925524700996+c.upper)) = pointBounds15770 := by
 decide +kernel
def cuts15771 : List PrefixCut := [⟨38,245175834,245175994⟩,
⟨102,660360540,660360973⟩,
⟨128,825071717,825072259⟩]
theorem checked15771 : checkPrefixCuts (2^48) 2071068673 9 Manual.Count131072.C015771.packed 128 cuts15771 = true := by
 decide +kernel
def pointBounds15771 : List (Nat × Nat × Nat) := [(2071107584,96926217758247,96926596224325),(2071173120,96926632942953,96927011409304)]
theorem point_links_checked15771 : (cuts15771.take 2).map (fun c => (2071068673-1+2*2^9*c.k,96925972582413+c.lower,96926351048331+c.upper)) = pointBounds15771 := by
 decide +kernel
def cuts15772 : List PrefixCut := [⟨38,246926979,246927138⟩,
⟨102,657600948,657601377⟩,
⟨128,827193797,827194339⟩]
theorem checked15772 : checkPrefixCuts (2^48) 2071199745 9 Manual.Count131072.C015772.packed 128 cuts15772 = true := by
 decide +kernel
def pointBounds15772 : List (Nat × Nat × Nat) := [(2071238656,96927044581109,96927423047728),(2071304192,96927455255078,96927833721967)]
theorem point_links_checked15772 : (cuts15772.take 2).map (fun c => (2071199745-1+2*2^9*c.k,96926797654130+c.lower,96927176120590+c.upper)) = pointBounds15772 := by
 decide +kernel
def cuts15773 : List PrefixCut := [⟨38,249493268,249493428⟩,
⟨102,656064553,656064976⟩,
⟨128,822793144,822793672⟩]
theorem checked15773 : checkPrefixCuts (2^48) 2071330817 9 Manual.Count131072.C015773.packed 128 cuts15773 = true := by
 decide +kernel
def pointBounds15773 : List (Nat × Nat × Nat) := [(2071369728,96927874341195,96928252808357),(2071435264,96928280912480,96928659379905)]
theorem point_links_checked15773 : (cuts15773.take 2).map (fun c => (2071330817-1+2*2^9*c.k,96927624847927+c.lower,96928003314929+c.upper)) = pointBounds15773 := by
 decide +kernel
def cuts15774 : List PrefixCut := [⟨38,243226947,243227107⟩,
⟨102,659963383,659963815⟩,
⟨128,824099779,824100319⟩]
theorem checked15774 : checkPrefixCuts (2^48) 2071461889 9 Manual.Count131072.C015774.packed 128 cuts15774 = true := by
 decide +kernel
def pointBounds15774 : List (Nat × Nat × Nat) := [(2071500800,96928690868018,96929069335708),(2071566336,96929107604454,96929486072416)]
theorem point_links_checked15774 : (cuts15774.take 2).map (fun c => (2071461889-1+2*2^9*c.k,96928447641071+c.lower,96928826108601+c.upper)) = pointBounds15774 := by
 decide +kernel
def cuts15775 : List PrefixCut := [⟨38,250276891,250277051⟩,
⟨102,670247840,670248270⟩,
⟨128,836819448,836819986⟩]
theorem checked15775 : checkPrefixCuts (2^48) 2071592961 9 Manual.Count131072.C015775.packed 128 cuts15775 = true := by
 decide +kernel
def pointBounds15775 : List (Nat × Nat × Nat) := [(2071631872,96929522017741,96929900485971),(2071697408,96929941988690,96930320457190)]
theorem point_links_checked15775 : (cuts15775.take 2).map (fun c => (2071592961-1+2*2^9*c.k,96929271740850+c.lower,96929650208920+c.upper)) = pointBounds15775 := by
 decide +kernel
def cuts15776 : List PrefixCut := [⟨38,250261045,250261208⟩,
⟨102,672379164,672379605⟩,
⟨128,840978076,840978625⟩]
theorem checked15776 : checkPrefixCuts (2^48) 2071724033 9 Manual.Count131072.C015776.packed 128 cuts15776 = true := by
 decide +kernel
def pointBounds15776 : List (Nat × Nat × Nat) := [(2071762944,96930358821343,96930737290114),(2071828480,96930780939462,96931159408511)]
theorem point_links_checked15776 : (cuts15776.take 2).map (fun c => (2071724033-1+2*2^9*c.k,96930108560298+c.lower,96930487028906+c.upper)) = pointBounds15776 := by
 decide +kernel
def cuts15777 : List PrefixCut := [⟨38,237338988,237339146⟩,
⟨102,648562248,648562672⟩,
⟨128,814433542,814434075⟩]
theorem checked15777 : checkPrefixCuts (2^48) 2071855105 9 Manual.Count131072.C015777.packed 128 cuts15777 = true := by
 decide +kernel
def pointBounds15777 : List (Nat × Nat × Nat) := [(2071894016,96931186877362,96931565346677),(2071959552,96931598100622,96931976570203)]
theorem point_links_checked15777 : (cuts15777.take 2).map (fun c => (2071855105-1+2*2^9*c.k,96930949538374+c.lower,96931328007531+c.upper)) = pointBounds15777 := by
 decide +kernel
def cuts15778 : List PrefixCut := [⟨38,244795540,244795695⟩,
⟨102,663600044,663600462⟩,
⟨128,828238286,828238812⟩]
theorem checked15778 : checkPrefixCuts (2^48) 2071986177 9 Manual.Count131072.C015778.packed 128 cuts15778 = true := by
 decide +kernel
def pointBounds15778 : List (Nat × Nat × Nat) := [(2072025088,96932008767456,96932387237301),(2072090624,96932427571960,96932806042068)]
theorem point_links_checked15778 : (cuts15778.take 2).map (fun c => (2071986177-1+2*2^9*c.k,96931763971916+c.lower,96932142441606+c.upper)) = pointBounds15778 := by
 decide +kernel
def cuts15779 : List PrefixCut := [⟨38,254288711,254288870⟩,
⟨102,664780844,664781271⟩,
⟨128,831717804,831718340⟩]
theorem checked15779 : checkPrefixCuts (2^48) 2072117249 9 Manual.Count131072.C015779.packed 128 cuts15779 = true := by
 decide +kernel
def pointBounds15779 : List (Nat × Nat × Nat) := [(2072156160,96932846498913,96933224969288),(2072221696,96933256991046,96933635461689)]
theorem point_links_checked15779 : (cuts15779.take 2).map (fun c => (2072117249-1+2*2^9*c.k,96932592210202+c.lower,96932970680418+c.upper)) = pointBounds15779 := by
 decide +kernel
def cuts15780 : List PrefixCut := [⟨38,241368836,241368994⟩,
⟨102,653872352,653872778⟩,
⟨128,827046648,827047184⟩]
theorem checked15780 : checkPrefixCuts (2^48) 2072248321 9 Manual.Count131072.C015780.packed 128 cuts15780 = true := by
 decide +kernel
def pointBounds15780 : List (Nat × Nat × Nat) := [(2072287232,96933665296842,96934043767752),(2072352768,96934077800358,96934456271536)]
theorem point_links_checked15780 : (cuts15780.take 2).map (fun c => (2072248321-1+2*2^9*c.k,96933423928006+c.lower,96933802398758+c.upper)) = pointBounds15780 := by
 decide +kernel
def cuts15781 : List PrefixCut := [⟨38,242032643,242032800⟩,
⟨102,654238523,654238947⟩,
⟨128,824957214,824957749⟩]
theorem checked15781 : checkPrefixCuts (2^48) 2072379393 9 Manual.Count131072.C015781.packed 128 cuts15781 = true := by
 decide +kernel
def pointBounds15781 : List (Nat × Nat × Nat) := [(2072418304,96934493007297,96934871478742),(2072483840,96934905213177,96935283684889)]
theorem point_links_checked15781 : (cuts15781.take 2).map (fun c => (2072379393-1+2*2^9*c.k,96934250974654+c.lower,96934629445942+c.upper)) = pointBounds15781 := by
 decide +kernel
def cuts15782 : List PrefixCut := [⟨38,254647931,254648093⟩,
⟨102,672803256,672803691⟩,
⟨128,837128236,837128777⟩]
theorem checked15782 : checkPrefixCuts (2^48) 2072510465 9 Manual.Count131072.C015782.packed 128 cuts15782 = true := by
 decide +kernel
def pointBounds15782 : List (Nat × Nat × Nat) := [(2072549376,96935330579799,96935709051784),(2072614912,96935748735124,96936127207382)]
theorem point_links_checked15782 : (cuts15782.take 2).map (fun c => (2072510465-1+2*2^9*c.k,96935075931868+c.lower,96935454403691+c.upper)) = pointBounds15782 := by
 decide +kernel
def cuts15783 : List PrefixCut := [⟨38,245397186,245397347⟩,
⟨102,663390145,663390575⟩,
⟨128,830013288,830013825⟩]
theorem checked15783 : checkPrefixCuts (2^48) 2072641537 9 Manual.Count131072.C015783.packed 128 cuts15783 = true := by
 decide +kernel
def pointBounds15783 : List (Nat × Nat × Nat) := [(2072680448,96936158457290,96936536929815),(2072745984,96936576450249,96936954923043)]
theorem point_links_checked15783 : (cuts15783.take 2).map (fun c => (2072641537-1+2*2^9*c.k,96935913060104+c.lower,96936291532468+c.upper)) = pointBounds15783 := by
 decide +kernel
def cuts15784 : List PrefixCut := [⟨38,244838465,244838621⟩,
⟨102,663619783,663620213⟩,
⟨128,829689216,829689756⟩]
theorem checked15784 : checkPrefixCuts (2^48) 2072772609 9 Manual.Count131072.C015784.packed 128 cuts15784 = true := by
 decide +kernel
def pointBounds15784 : List (Nat × Nat × Nat) := [(2072811520,96936987911857,96937366384914),(2072877056,96937406693175,96937785166506)]
theorem point_links_checked15784 : (cuts15784.take 2).map (fun c => (2072772609-1+2*2^9*c.k,96936743073392+c.lower,96937121546293+c.upper)) = pointBounds15784 := by
 decide +kernel
def cuts15785 : List PrefixCut := [⟨38,238712593,238712747⟩,
⟨102,651900358,651900778⟩,
⟨128,818366652,818367181⟩]
theorem checked15785 : checkPrefixCuts (2^48) 2072903681 9 Manual.Count131072.C015785.packed 128 cuts15785 = true := by
 decide +kernel
def pointBounds15785 : List (Nat × Nat × Nat) := [(2072942592,96937811475201,96938189948796),(2073008128,96938224662966,96938603136827)]
theorem point_links_checked15785 : (cuts15785.take 2).map (fun c => (2072903681-1+2*2^9*c.k,96937572762608+c.lower,96937951236049+c.upper)) = pointBounds15785 := by
 decide +kernel
def cuts15786 : List PrefixCut := [⟨38,248201964,248202125⟩,
⟨102,664214969,664215395⟩,
⟨128,830534975,830535509⟩]
theorem checked15786 : checkPrefixCuts (2^48) 2073034753 9 Manual.Count131072.C015786.packed 128 cuts15786 = true := by
 decide +kernel
def pointBounds15786 : List (Nat × Nat × Nat) := [(2073073664,96938639331224,96939017805355),(2073139200,96939055344229,96939433818625)]
theorem point_links_checked15786 : (cuts15786.take 2).map (fun c => (2073034753-1+2*2^9*c.k,96938391129260+c.lower,96938769603230+c.upper)) = pointBounds15786 := by
 decide +kernel
def cuts15787 : List PrefixCut := [⟨38,247778939,247779101⟩,
⟨102,659285322,659285749⟩,
⟨128,828581586,828582121⟩]
theorem checked15787 : checkPrefixCuts (2^48) 2073165825 9 Manual.Count131072.C015787.packed 128 cuts15787 = true := by
 decide +kernel
def pointBounds15787 : List (Nat × Nat × Nat) := [(2073204736,96939469443174,96939847917840),(2073270272,96939880949557,96940259424488)]
theorem point_links_checked15787 : (cuts15787.take 2).map (fun c => (2073165825-1+2*2^9*c.k,96939221664235+c.lower,96939600138739+c.upper)) = pointBounds15787 := by
 decide +kernel
def cuts15788 : List PrefixCut := [⟨38,245455312,245455473⟩,
⟨102,668339267,668339705⟩,
⟨128,836946082,836946630⟩]
theorem checked15788 : checkPrefixCuts (2^48) 2073296897 9 Manual.Count131072.C015788.packed 128 cuts15788 = true := by
 decide +kernel
def pointBounds15788 : List (Nat × Nat × Nat) := [(2073335808,96940295701133,96940674176333),(2073401344,96940718585088,96941097060565)]
theorem point_links_checked15788 : (cuts15788.take 2).map (fun c => (2073296897-1+2*2^9*c.k,96940050245821+c.lower,96940428720860+c.upper)) = pointBounds15788 := by
 decide +kernel
def cuts15789 : List PrefixCut := [⟨38,248833638,248833798⟩,
⟨102,668840126,668840558⟩,
⟨128,838522216,838522755⟩]
theorem checked15789 : checkPrefixCuts (2^48) 2073427969 9 Manual.Count131072.C015789.packed 128 cuts15789 = true := by
 decide +kernel
def pointBounds15789 : List (Nat × Nat × Nat) := [(2073466880,96941136025541,96941514501288),(2073532416,96941556032029,96941934508048)]
theorem point_links_checked15789 : (cuts15789.take 2).map (fun c => (2073427969-1+2*2^9*c.k,96940887191903+c.lower,96941265667490+c.upper)) = pointBounds15789 := by
 decide +kernel
def cuts15790 : List PrefixCut := [⟨38,250582580,250582740⟩,
⟨102,665268668,665269101⟩,
⟨128,836297415,836297961⟩]
theorem checked15790 : checkPrefixCuts (2^48) 2073559041 9 Manual.Count131072.C015790.packed 128 cuts15790 = true := by
 decide +kernel
def pointBounds15790 : List (Nat × Nat × Nat) := [(2073597952,96941976296699,96942354772985),(2073663488,96942390982787,96942769459346)]
theorem point_links_checked15790 : (cuts15790.take 2).map (fun c => (2073559041-1+2*2^9*c.k,96941725714119+c.lower,96942104190245+c.upper)) = pointBounds15790 := by
 decide +kernel
def cuts15791 : List PrefixCut := [⟨38,244594402,244594562⟩,
⟨102,663461924,663462353⟩,
⟨128,834208402,834208939⟩]
theorem checked15791 : checkPrefixCuts (2^48) 2073690113 9 Manual.Count131072.C015791.packed 128 cuts15791 = true := by
 decide +kernel
def pointBounds15791 : List (Nat × Nat × Nat) := [(2073729024,96942806605936,96943185082768),(2073794560,96943225473458,96943603950559)]
theorem point_links_checked15791 : (cuts15791.take 2).map (fun c => (2073690113-1+2*2^9*c.k,96942562011534+c.lower,96942940488206+c.upper)) = pointBounds15791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000180
