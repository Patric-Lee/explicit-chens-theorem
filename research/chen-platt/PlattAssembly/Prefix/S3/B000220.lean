import PlattAssemblyKernel
import PlattCertificates.Count131072.C027040
import PlattCertificates.Count131072.C027041
import PlattCertificates.Count131072.C027042
import PlattCertificates.Count131072.C027043
import PlattCertificates.Count131072.C027044
import PlattCertificates.Count131072.C027045
import PlattCertificates.Count131072.C027046
import PlattCertificates.Count131072.C027047
import PlattCertificates.Count131072.C027048
import PlattCertificates.Count131072.C027049
import PlattCertificates.Count131072.C027050
import PlattCertificates.Count131072.C027051
import PlattCertificates.Count131072.C027052
import PlattCertificates.Count131072.C027053
import PlattCertificates.Count131072.C027054
import PlattCertificates.Count131072.C027055
import PlattCertificates.Count131072.C027056
import PlattCertificates.Count131072.C027057
import PlattCertificates.Count131072.C027058
import PlattCertificates.Count131072.C027059
import PlattCertificates.Count131072.C027060
import PlattCertificates.Count131072.C027061
import PlattCertificates.Count131072.C027062
import PlattCertificates.Count131072.C027063
import PlattCertificates.Count131072.C027064
import PlattCertificates.Count131072.C027065
import PlattCertificates.Count131072.C027066
import PlattCertificates.Count131072.C027067
import PlattCertificates.Count131072.C027068
import PlattCertificates.Count131072.C027069
import PlattCertificates.Count131072.C027070
import PlattCertificates.Count131072.C027071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27040 : List PrefixCut := [⟨46,165641488,165641581⟩,
⟨128,471374512,471374772⟩]
theorem checked27040 : checkPrefixCuts (2^48) 3548119041 9 Manual.Count131072.C027040.packed 128 cuts27040 = true := by
 decide +kernel
def pointBounds27040 : List (Nat × Nat × Nat) := [(3548166144,103902952243509,103903334822665)]
theorem point_links_checked27040 : (cuts27040.take 1).map (fun c => (3548119041-1+2*2^9*c.k,103902786602021+c.lower,103903169181084+c.upper)) = pointBounds27040 := by
 decide +kernel
def cuts27041 : List PrefixCut := [⟨27,96779541,96779596⟩,
⟨128,476354595,476354863⟩]
theorem checked27041 : checkPrefixCuts (2^48) 3548250113 9 Manual.Count131072.C027041.packed 128 cuts27041 = true := by
 decide +kernel
def pointBounds27041 : List (Nat × Nat × Nat) := [(3548277760,103903354756074,103903737335452)]
theorem point_links_checked27041 : (cuts27041.take 1).map (fun c => (3548250113-1+2*2^9*c.k,103903257976533+c.lower,103903640555856+c.upper)) = pointBounds27041 := by
 decide +kernel
def cuts27042 : List PrefixCut := [⟨8,29508820,29508836⟩,
⟨117,432313272,432313513⟩,
⟨128,472212276,472212541⟩]
theorem checked27042 : checkPrefixCuts (2^48) 3548381185 9 Manual.Count131072.C027042.packed 128 cuts27042 = true := by
 decide +kernel
def pointBounds27042 : List (Nat × Nat × Nat) := [(3548389376,103903763839948,103904146419555),(3548500992,103904166644400,103904549224232)]
theorem point_links_checked27042 : (cuts27042.take 2).map (fun c => (3548381185-1+2*2^9*c.k,103903734331128+c.lower,103904116910719+c.upper)) = pointBounds27042 := by
 decide +kernel
def cuts27043 : List PrefixCut := [⟨98,364717186,364717389⟩,
⟨128,477033393,477033658⟩]
theorem checked27043 : checkPrefixCuts (2^48) 3548512257 9 Manual.Count131072.C027043.packed 128 cuts27043 = true := by
 decide +kernel
def pointBounds27043 : List (Nat × Nat × Nat) := [(3548612608,103904571260590,103904953840649)]
theorem point_links_checked27043 : (cuts27043.take 1).map (fun c => (3548512257-1+2*2^9*c.k,103904206543404+c.lower,103904589123260+c.upper)) = pointBounds27043 := by
 decide +kernel
def cuts27044 : List PrefixCut := [⟨79,292287246,292287406⟩,
⟨128,473922365,473922624⟩]
theorem checked27044 : checkPrefixCuts (2^48) 3548643329 9 Manual.Count131072.C027044.packed 128 cuts27044 = true := by
 decide +kernel
def pointBounds27044 : List (Nat × Nat × Nat) := [(3548724224,103904975864043,103905358444324)]
theorem point_links_checked27044 : (cuts27044.take 1).map (fun c => (3548643329-1+2*2^9*c.k,103904683576797+c.lower,103905066156918+c.upper)) = pointBounds27044 := by
 decide +kernel
def cuts27045 : List PrefixCut := [⟨60,220814075,220814199⟩,
⟨128,475808370,475808632⟩]
theorem checked27045 : checkPrefixCuts (2^48) 3548774401 9 Manual.Count131072.C027045.packed 128 cuts27045 = true := by
 decide +kernel
def pointBounds27045 : List (Nat × Nat × Nat) := [(3548835840,103905378313237,103905760893741)]
theorem point_links_checked27045 : (cuts27045.take 1).map (fun c => (3548774401-1+2*2^9*c.k,103905157499162+c.lower,103905540079542+c.upper)) = pointBounds27045 := by
 decide +kernel
def cuts27046 : List PrefixCut := [⟨41,149821651,149821738⟩,
⟨128,476345971,476346239⟩]
theorem checked27046 : checkPrefixCuts (2^48) 3548905473 9 Manual.Count131072.C027046.packed 128 cuts27046 = true := by
 decide +kernel
def pointBounds27046 : List (Nat × Nat × Nat) := [(3548947456,103905783129183,103906165709912)]
theorem point_links_checked27046 : (cuts27046.take 1).map (fun c => (3548905473-1+2*2^9*c.k,103905633307532+c.lower,103906015888174+c.upper)) = pointBounds27046 := by
 decide +kernel
def cuts27047 : List PrefixCut := [⟨22,79309982,79310025⟩,
⟨128,467683778,467684041⟩]
theorem checked27047 : checkPrefixCuts (2^48) 3549036545 9 Manual.Count131072.C027047.packed 128 cuts27047 = true := by
 decide +kernel
def pointBounds27047 : List (Nat × Nat × Nat) := [(3549059072,103906188963485,103906571544438)]
theorem point_links_checked27047 : (cuts27047.take 1).map (fun c => (3549036545-1+2*2^9*c.k,103906109653503+c.lower,103906492234413+c.upper)) = pointBounds27047 := by
 decide +kernel
def cuts27048 : List PrefixCut := [⟨3,10389253,10389258⟩,
⟨112,412391333,412391556⟩,
⟨128,470838787,470839042⟩]
theorem checked27048 : checkPrefixCuts (2^48) 3549167617 9 Manual.Count131072.C027048.packed 128 cuts27048 = true := by
 decide +kernel
def pointBounds27048 : List (Nat × Nat × Nat) := [(3549170688,103906587726534,103906970307712),(3549282304,103906989728614,103907372310010)]
theorem point_links_checked27048 : (cuts27048.take 2).map (fun c => (3549167617-1+2*2^9*c.k,103906577337281+c.lower,103906959918454+c.upper)) = pointBounds27048 := by
 decide +kernel
def cuts27049 : List PrefixCut := [⟨93,340369830,340370023⟩,
⟨128,472090180,472090446⟩]
theorem checked27049 : checkPrefixCuts (2^48) 3549298689 9 Manual.Count131072.C027049.packed 128 cuts27049 = true := by
 decide +kernel
def pointBounds27049 : List (Nat × Nat × Nat) := [(3549393920,103907388545898,103907771127519)]
theorem point_links_checked27049 : (cuts27049.take 1).map (fun c => (3549298689-1+2*2^9*c.k,103907048176068+c.lower,103907430757496+c.upper)) = pointBounds27049 := by
 decide +kernel
def cuts27050 : List PrefixCut := [⟨74,277631430,277631581⟩,
⟨128,479923501,479923769⟩]
theorem checked27050 : checkPrefixCuts (2^48) 3549429761 9 Manual.Count131072.C027050.packed 128 cuts27050 = true := by
 decide +kernel
def pointBounds27050 : List (Nat × Nat × Nat) := [(3549505536,103907797897678,103908180479523)]
theorem point_links_checked27050 : (cuts27050.take 1).map (fun c => (3549429761-1+2*2^9*c.k,103907520266248+c.lower,103907902847942+c.upper)) = pointBounds27050 := by
 decide +kernel
def cuts27051 : List PrefixCut := [⟨55,202526770,202526884⟩,
⟨128,471976038,471976296⟩]
theorem checked27051 : checkPrefixCuts (2^48) 3549560833 9 Manual.Count131072.C027051.packed 128 cuts27051 = true := by
 decide +kernel
def pointBounds27051 : List (Nat × Nat × Nat) := [(3549617152,103908202716519,103908585298595)]
theorem point_links_checked27051 : (cuts27051.take 1).map (fun c => (3549560833-1+2*2^9*c.k,103908000189749+c.lower,103908382771711+c.upper)) = pointBounds27051 := by
 decide +kernel
def cuts27052 : List PrefixCut := [⟨36,133136588,133136661⟩,
⟨128,472989438,472989701⟩]
theorem checked27052 : checkPrefixCuts (2^48) 3549691905 9 Manual.Count131072.C027052.packed 128 cuts27052 = true := by
 decide +kernel
def pointBounds27052 : List (Nat × Nat × Nat) := [(3549728768,103908605302375,103908987884668)]
theorem point_links_checked27052 : (cuts27052.take 1).map (fun c => (3549691905-1+2*2^9*c.k,103908472165787+c.lower,103908854748007+c.upper)) = pointBounds27052 := by
 decide +kernel
def cuts27053 : List PrefixCut := [⟨17,59469345,59469378⟩,
⟨126,458144588,458144841⟩,
⟨128,466707882,466708139⟩]
theorem checked27053 : checkPrefixCuts (2^48) 3549822977 9 Manual.Count131072.C027053.packed 128 cuts27053 = true := by
 decide +kernel
def pointBounds27053 : List (Nat × Nat × Nat) := [(3549840384,103909004624570,103909387207086),(3549952000,103909403299813,103909785882549)]
theorem point_links_checked27053 : (cuts27053.take 2).map (fun c => (3549822977-1+2*2^9*c.k,103908945155225+c.lower,103909327737708+c.upper)) = pointBounds27053 := by
 decide +kernel
def cuts27054 : List PrefixCut := [⟨107,394143124,394143340⟩,
⟨128,473588741,473589002⟩]
theorem checked27054 : checkPrefixCuts (2^48) 3549954049 9 Manual.Count131072.C027054.packed 128 cuts27054 = true := by
 decide +kernel
def pointBounds27054 : List (Nat × Nat × Nat) := [(3550063616,103909806006231,103910188589187)]
theorem point_links_checked27054 : (cuts27054.take 1).map (fun c => (3549954049-1+2*2^9*c.k,103909411863107+c.lower,103909794445847+c.upper)) = pointBounds27054 := by
 decide +kernel
def cuts27055 : List PrefixCut := [⟨88,328084609,328084792⟩,
⟨128,472540654,472540917⟩]
theorem checked27055 : checkPrefixCuts (2^48) 3550085121 9 Manual.Count131072.C027055.packed 128 cuts27055 = true := by
 decide +kernel
def pointBounds27055 : List (Nat × Nat × Nat) := [(3550175232,103910213536457,103910596119641)]
theorem point_links_checked27055 : (cuts27055.take 1).map (fun c => (3550085121-1+2*2^9*c.k,103909885451848+c.lower,103910268034849+c.upper)) = pointBounds27055 := by
 decide +kernel
def cuts27056 : List PrefixCut := [⟨69,256797913,256798057⟩,
⟨128,475139481,475139747⟩]
theorem checked27056 : checkPrefixCuts (2^48) 3550216193 9 Manual.Count131072.C027056.packed 128 cuts27056 = true := by
 decide +kernel
def pointBounds27056 : List (Nat × Nat × Nat) := [(3550286848,103910614790415,103910997373823)]
theorem point_links_checked27056 : (cuts27056.take 1).map (fun c => (3550216193-1+2*2^9*c.k,103910357992502+c.lower,103910740575766+c.upper)) = pointBounds27056 := by
 decide +kernel
def cuts27057 : List PrefixCut := [⟨50,181869204,181869305⟩,
⟨128,472902069,472902332⟩]
theorem checked27057 : checkPrefixCuts (2^48) 3550347265 9 Manual.Count131072.C027057.packed 128 cuts27057 = true := by
 decide +kernel
def pointBounds27057 : List (Nat × Nat × Nat) := [(3550398464,103911015001187,103911397584818)]
theorem point_links_checked27057 : (cuts27057.take 1).map (fun c => (3550347265-1+2*2^9*c.k,103910833131983+c.lower,103911215715513+c.upper)) = pointBounds27057 := by
 decide +kernel
def cuts27058 : List PrefixCut := [⟨31,115983234,115983299⟩,
⟨128,477165600,477165866⟩]
theorem checked27058 : checkPrefixCuts (2^48) 3550478337 9 Manual.Count131072.C027058.packed 128 cuts27058 = true := by
 decide +kernel
def pointBounds27058 : List (Nat × Nat × Nat) := [(3550510080,103911422017286,103911804601144)]
theorem point_links_checked27058 : (cuts27058.take 1).map (fun c => (3550478337-1+2*2^9*c.k,103911306034052+c.lower,103911688617845+c.upper)) = pointBounds27058 := by
 decide +kernel
def cuts27059 : List PrefixCut := [⟨12,42967030,42967054⟩,
⟨121,445201140,445201390⟩,
⟨128,469458449,469458713⟩]
theorem checked27059 : checkPrefixCuts (2^48) 3550609409 9 Manual.Count131072.C027059.packed 128 cuts27059 = true := by
 decide +kernel
def pointBounds27059 : List (Nat × Nat × Nat) := [(3550621696,103911826166682,103912208750765),(3550733312,103912228400792,103912610985101)]
theorem point_links_checked27059 : (cuts27059.take 2).map (fun c => (3550609409-1+2*2^9*c.k,103911783199652+c.lower,103912165783711+c.upper)) = pointBounds27059 := by
 decide +kernel
def cuts27060 : List PrefixCut := [⟨102,379311816,379312028⟩,
⟨128,475941382,475941649⟩]
theorem checked27060 : checkPrefixCuts (2^48) 3550740481 9 Manual.Count131072.C027060.packed 128 cuts27060 = true := by
 decide +kernel
def pointBounds27060 : List (Nat × Nat × Nat) := [(3550844928,103912631969917,103913014554452)]
theorem point_links_checked27060 : (cuts27060.take 1).map (fun c => (3550740481-1+2*2^9*c.k,103912252658101+c.lower,103912635242424+c.upper)) = pointBounds27060 := by
 decide +kernel
def cuts27061 : List PrefixCut := [⟨83,306926821,306926994⟩,
⟨128,474893234,474893503⟩]
theorem checked27061 : checkPrefixCuts (2^48) 3550871553 9 Manual.Count131072.C027061.packed 128 cuts27061 = true := by
 decide +kernel
def pointBounds27061 : List (Nat × Nat × Nat) := [(3550956544,103913035526304,103913418111067)]
theorem point_links_checked27061 : (cuts27061.take 1).map (fun c => (3550871553-1+2*2^9*c.k,103912728599483+c.lower,103913111184073+c.upper)) = pointBounds27061 := by
 decide +kernel
def cuts27062 : List PrefixCut := [⟨64,235656576,235656706⟩,
⟨128,472022206,472022469⟩]
theorem checked27062 : checkPrefixCuts (2^48) 3551002625 9 Manual.Count131072.C027062.packed 128 cuts27062 = true := by
 decide +kernel
def pointBounds27062 : List (Nat × Nat × Nat) := [(3551068160,103913439149293,103913821734282)]
theorem point_links_checked27062 : (cuts27062.take 1).map (fun c => (3551002625-1+2*2^9*c.k,103913203492717+c.lower,103913586077576+c.upper)) = pointBounds27062 := by
 decide +kernel
def cuts27063 : List PrefixCut := [⟨45,170335921,170336014⟩,
⟨128,475016843,475017107⟩]
theorem checked27063 : checkPrefixCuts (2^48) 3551133697 9 Manual.Count131072.C027063.packed 128 cuts27063 = true := by
 decide +kernel
def pointBounds27063 : List (Nat × Nat × Nat) := [(3551179776,103913845850844,103914228436059)]
theorem point_links_checked27063 : (cuts27063.take 1).map (fun c => (3551133697-1+2*2^9*c.k,103913675514923+c.lower,103914058100045+c.upper)) = pointBounds27063 := by
 decide +kernel
def cuts27064 : List PrefixCut := [⟨26,95984061,95984116⟩,
⟨128,475157697,475157960⟩]
theorem checked27064 : checkPrefixCuts (2^48) 3551264769 9 Manual.Count131072.C027064.packed 128 cuts27064 = true := by
 decide +kernel
def pointBounds27064 : List (Nat × Nat × Nat) := [(3551291392,103914246515827,103914629101268)]
theorem point_links_checked27064 : (cuts27064.take 1).map (fun c => (3551264769-1+2*2^9*c.k,103914150531766+c.lower,103914533117152+c.upper)) = pointBounds27064 := by
 decide +kernel
def cuts27065 : List PrefixCut := [⟨7,26551249,26551263⟩,
⟨116,431470837,431471076⟩,
⟨128,477121575,477121839⟩]
theorem checked27065 : checkPrefixCuts (2^48) 3551395841 9 Manual.Count131072.C027065.packed 128 cuts27065 = true := by
 decide +kernel
def pointBounds27065 : List (Nat × Nat × Nat) := [(3551403008,103914652240712,103915034826375),(3551514624,103915057160300,103915439746188)]
theorem point_links_checked27065 : (cuts27065.take 2).map (fun c => (3551395841-1+2*2^9*c.k,103914625689463+c.lower,103915008275112+c.upper)) = pointBounds27065 := by
 decide +kernel
def cuts27066 : List PrefixCut := [⟨97,352836591,352836793⟩,
⟨128,468623830,468624095⟩]
theorem checked27066 : checkPrefixCuts (2^48) 3551526913 9 Manual.Count131072.C027066.packed 128 cuts27066 = true := by
 decide +kernel
def pointBounds27066 : List (Nat × Nat × Nat) := [(3551626240,103915455647629,103915838233744)]
theorem point_links_checked27066 : (cuts27066.take 1).map (fun c => (3551526913-1+2*2^9*c.k,103915102811038+c.lower,103915485396951+c.upper)) = pointBounds27066 := by
 decide +kernel
def cuts27067 : List PrefixCut := [⟨78,282291309,282291471⟩,
⟨128,461791056,461791322⟩]
theorem checked27067 : checkPrefixCuts (2^48) 3551657985 9 Manual.Count131072.C027067.packed 128 cuts27067 = true := by
 decide +kernel
def pointBounds27067 : List (Nat × Nat × Nat) := [(3551737856,103915853726177,103916236312517)]
theorem point_links_checked27067 : (cuts27067.take 1).map (fun c => (3551657985-1+2*2^9*c.k,103915571434868+c.lower,103915954021046+c.upper)) = pointBounds27067 := by
 decide +kernel
def cuts27068 : List PrefixCut := [⟨59,219913462,219913587⟩,
⟨128,474374413,474374681⟩]
theorem checked27068 : checkPrefixCuts (2^48) 3551789057 9 Manual.Count131072.C027068.packed 128 cuts27068 = true := by
 decide +kernel
def pointBounds27068 : List (Nat × Nat × Nat) := [(3551849472,103916253139386,103916635725955)]
theorem point_links_checked27068 : (cuts27068.take 1).map (fun c => (3551789057-1+2*2^9*c.k,103916033225924+c.lower,103916415812368+c.upper)) = pointBounds27068 := by
 decide +kernel
def cuts27069 : List PrefixCut := [⟨40,144860556,144860642⟩,
⟨128,471583224,471583495⟩]
theorem checked27069 : checkPrefixCuts (2^48) 3551920129 9 Manual.Count131072.C027069.packed 128 cuts27069 = true := by
 decide +kernel
def pointBounds27069 : List (Nat × Nat × Nat) := [(3551961088,103916652460893,103917035047691)]
theorem point_links_checked27069 : (cuts27069.take 1).map (fun c => (3551920129-1+2*2^9*c.k,103916507600337+c.lower,103916890187049+c.upper)) = pointBounds27069 := by
 decide +kernel
def cuts27070 : List PrefixCut := [⟨21,77499336,77499378⟩,
⟨128,465622766,465623025⟩]
theorem checked27070 : checkPrefixCuts (2^48) 3552051201 9 Manual.Count131072.C027070.packed 128 cuts27070 = true := by
 decide +kernel
def pointBounds27070 : List (Nat × Nat × Nat) := [(3552072704,103917056682897,103917439269922)]
theorem point_links_checked27070 : (cuts27070.take 1).map (fun c => (3552051201-1+2*2^9*c.k,103916979183561+c.lower,103917361770544+c.upper)) = pointBounds27070 := by
 decide +kernel
def cuts27071 : List PrefixCut := [⟨2,7210837,7210841⟩,
⟨111,404751341,404751563⟩,
⟨128,468854291,468854546⟩]
theorem checked27071 : checkPrefixCuts (2^48) 3552182273 9 Manual.Count131072.C027071.packed 128 cuts27071 = true := by
 decide +kernel
def pointBounds27071 : List (Nat × Nat × Nat) := [(3552184320,103917452017164,103917834604410),(3552295936,103917849557668,103918232145132)]
theorem point_links_checked27071 : (cuts27071.take 2).map (fun c => (3552182273-1+2*2^9*c.k,103917444806327+c.lower,103917827393569+c.upper)) = pointBounds27071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000220
