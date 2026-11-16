import PlattAssemblyKernel
import PlattCertificates.Count131072.C014032
import PlattCertificates.Count131072.C014033
import PlattCertificates.Count131072.C014034
import PlattCertificates.Count131072.C014035
import PlattCertificates.Count131072.C014036
import PlattCertificates.Count131072.C014037
import PlattCertificates.Count131072.C014038
import PlattCertificates.Count131072.C014039
import PlattCertificates.Count131072.C014040
import PlattCertificates.Count131072.C014041
import PlattCertificates.Count131072.C014042
import PlattCertificates.Count131072.C014043
import PlattCertificates.Count131072.C014044
import PlattCertificates.Count131072.C014045
import PlattCertificates.Count131072.C014046
import PlattCertificates.Count131072.C014047
import PlattCertificates.Count131072.C014048
import PlattCertificates.Count131072.C014049
import PlattCertificates.Count131072.C014050
import PlattCertificates.Count131072.C014051
import PlattCertificates.Count131072.C014052
import PlattCertificates.Count131072.C014053
import PlattCertificates.Count131072.C014054
import PlattCertificates.Count131072.C014055
import PlattCertificates.Count131072.C014056
import PlattCertificates.Count131072.C014057
import PlattCertificates.Count131072.C014058
import PlattCertificates.Count131072.C014059
import PlattCertificates.Count131072.C014060
import PlattCertificates.Count131072.C014061
import PlattCertificates.Count131072.C014062
import PlattCertificates.Count131072.C014063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14032 : List PrefixCut := [⟨54,393388772,393389040⟩,
⟨111,809213594,809214149⟩,
⟨128,937180532,937181175⟩]
theorem checked14032 : checkPrefixCuts (2^48) 1843134465 9 Manual.Count131072.C014032.packed 128 cuts14032 = true := by
 decide +kernel
def pointBounds14032 : List (Nat × Nat × Nat) := [(1843189760,95392350003519,95392727442673),(1843248128,95392765828341,95393143267782)]
theorem point_links_checked14032 : (cuts14032.take 2).map (fun c => (1843134465-1+2*2^9*c.k,95391956614747+c.lower,95392334053633+c.upper)) = pointBounds14032 := by
 decide +kernel
def cuts14033 : List PrefixCut := [⟨40,295174443,295174647⟩,
⟨97,711583695,711584191⟩,
⟨128,940626116,940626770⟩]
theorem checked14033 : checkPrefixCuts (2^48) 1843265537 9 Manual.Count131072.C014033.packed 128 cuts14033 = true := by
 decide +kernel
def pointBounds14033 : List (Nat × Nat × Nat) := [(1843306496,95393188969722,95393566409455),(1843364864,95393605378974,95393982818999)]
theorem point_links_checked14033 : (cuts14033.take 2).map (fun c => (1843265537-1+2*2^9*c.k,95392893795279+c.lower,95393271234808+c.upper)) = pointBounds14033 := by
 decide +kernel
def cuts14034 : List PrefixCut := [⟨26,195293725,195293859⟩,
⟨83,615951885,615952307⟩,
⟨128,941322981,941323627⟩]
theorem checked14034 : checkPrefixCuts (2^48) 1843396609 9 Manual.Count131072.C014034.packed 128 cuts14034 = true := by
 decide +kernel
def pointBounds14034 : List (Nat × Nat × Nat) := [(1843423232,95394029715120,95394407155437),(1843481600,95394450373280,95394827813885)]
theorem point_links_checked14034 : (cuts14034.take 2).map (fun c => (1843396609-1+2*2^9*c.k,95393834421395+c.lower,95394211861578+c.upper)) = pointBounds14034 := by
 decide +kernel
def cuts14035 : List PrefixCut := [⟨12,86570836,86570896⟩,
⟨69,509339823,509340177⟩,
⟨126,927820578,927821222⟩,
⟨128,943545792,943546446⟩]
theorem checked14035 : checkPrefixCuts (2^48) 1843527681 9 Manual.Count131072.C014035.packed 128 cuts14035 = true := by
 decide +kernel
def pointBounds14035 : List (Nat × Nat × Nat) := [(1843539968,95394862315212,95395239756101),(1843598336,95395285084199,95395662525382),(1843656704,95395703564954,95396081006427)]
theorem point_links_checked14035 : (cuts14035.take 3).map (fun c => (1843527681-1+2*2^9*c.k,95394775744376+c.lower,95395153185205+c.upper)) = pointBounds14035 := by
 decide +kernel
def cuts14036 : List PrefixCut := [⟨55,402131601,402131879⟩,
⟨112,820738487,820739052⟩,
⟨128,940883252,940883899⟩]
theorem checked14036 : checkPrefixCuts (2^48) 1843658753 9 Manual.Count131072.C014036.packed 128 cuts14036 = true := by
 decide +kernel
def pointBounds14036 : List (Nat × Nat × Nat) := [(1843715072,95396121421769,95396498863530),(1843773440,95396540028655,95396917470703)]
theorem point_links_checked14036 : (cuts14036.take 2).map (fun c => (1843658753-1+2*2^9*c.k,95395719290168+c.lower,95396096731651+c.upper)) = pointBounds14036 := by
 decide +kernel
def cuts14037 : List PrefixCut := [⟨41,295090392,295090596⟩,
⟨98,708938560,708939049⟩,
⟨128,928604010,928604651⟩]
theorem checked14037 : checkPrefixCuts (2^48) 1843789825 9 Manual.Count131072.C014037.packed 128 cuts14037 = true := by
 decide +kernel
def pointBounds14037 : List (Nat × Nat × Nat) := [(1843831808,95396955263812,95397332706146),(1843890176,95397369111980,95397746554599)]
theorem point_links_checked14037 : (cuts14037.take 2).map (fun c => (1843789825-1+2*2^9*c.k,95396660173420+c.lower,95397037615550+c.upper)) = pointBounds14037 := by
 decide +kernel
def cuts14038 : List PrefixCut := [⟨27,197985829,197985968⟩,
⟨84,621119081,621119509⟩,
⟨128,941055056,941055711⟩]
theorem checked14038 : checkPrefixCuts (2^48) 1843920897 9 Manual.Count131072.C014038.packed 128 cuts14038 = true := by
 decide +kernel
def pointBounds14038 : List (Nat × Nat × Nat) := [(1843948544,95397786763259,95398164206169),(1844006912,95398209896511,95398587339710)]
theorem point_links_checked14038 : (cuts14038.take 2).map (fun c => (1843920897-1+2*2^9*c.k,95397588777430+c.lower,95397966220201+c.upper)) = pointBounds14038 := by
 decide +kernel
def cuts14039 : List PrefixCut := [⟨13,94025492,94025558⟩,
⟨70,506905457,506905812⟩,
⟨127,929845905,929846560⟩,
⟨128,936408932,936409592⟩]
theorem checked14039 : checkPrefixCuts (2^48) 1844051969 9 Manual.Count131072.C014039.packed 128 cuts14039 = true := by
 decide +kernel
def pointBounds14039 : List (Nat × Nat × Nat) := [(1844065280,95398623857978,95399001301470),(1844123648,95399036737943,95399414181724),(1844182016,95399459678391,95399837122472)]
theorem point_links_checked14039 : (cuts14039.take 3).map (fun c => (1844051969-1+2*2^9*c.k,95398529832486+c.lower,95398907275912+c.upper)) = pointBounds14039 := by
 decide +kernel
def cuts14040 : List PrefixCut := [⟨56,411480020,411480305⟩,
⟨113,822641844,822642413⟩,
⟨128,933137474,933138118⟩]
theorem checked14040 : checkPrefixCuts (2^48) 1844183041 9 Manual.Count131072.C014040.packed 128 cuts14040 = true := by
 decide +kernel
def pointBounds14040 : List (Nat × Nat × Nat) := [(1844240384,95399877721438,95400255165809),(1844298752,95400288883262,95400666327917)]
theorem point_links_checked14040 : (cuts14040.take 2).map (fun c => (1844183041-1+2*2^9*c.k,95399466241418+c.lower,95399843685504+c.upper)) = pointBounds14040 := by
 decide +kernel
def cuts14041 : List PrefixCut := [⟨42,303095072,303095283⟩,
⟨99,728271229,728271734⟩,
⟨128,945279860,945280516⟩]
theorem checked14041 : checkPrefixCuts (2^48) 1844314113 9 Manual.Count131072.C014041.packed 128 cuts14041 = true := by
 decide +kernel
def pointBounds14041 : List (Nat × Nat × Nat) := [(1844357120,95400702473964,95401079918905),(1844415488,95401127650121,95401505095356)]
theorem point_links_checked14041 : (cuts14041.take 2).map (fun c => (1844314113-1+2*2^9*c.k,95400399378892+c.lower,95400776823622+c.upper)) = pointBounds14041 := by
 decide +kernel
def cuts14042 : List PrefixCut := [⟨28,205101965,205102107⟩,
⟨85,618195681,618196112⟩,
⟨128,931631536,931632184⟩]
theorem checked14042 : checkPrefixCuts (2^48) 1844445185 9 Manual.Count131072.C014042.packed 128 cuts14042 = true := by
 decide +kernel
def pointBounds14042 : List (Nat × Nat × Nat) := [(1844473856,95401549760717,95401927206245),(1844532224,95401962854433,95402340300250)]
theorem point_links_checked14042 : (cuts14042.take 2).map (fun c => (1844445185-1+2*2^9*c.k,95401344658752+c.lower,95401722104138+c.upper)) = pointBounds14042 := by
 decide +kernel
def cuts14043 : List PrefixCut := [⟨14,101781108,101781179⟩,
⟨71,516069461,516069814⟩,
⟨128,930344623,930345262⟩]
theorem checked14043 : checkPrefixCuts (2^48) 1844576257 9 Manual.Count131072.C014043.packed 128 cuts14043 = true := by
 decide +kernel
def pointBounds14043 : List (Nat × Nat × Nat) := [(1844590592,95402378071396,95402755517501),(1844648960,95402792359749,95403169806136),(1844707328,95403206634911,95403584081584)]
theorem point_links_checked14043 : (cuts14043.take 3).map (fun c => (1844576257-1+2*2^9*c.k,95402276290288+c.lower,95402653736322+c.upper)) = pointBounds14043 := by
 decide +kernel
def cuts14044 : List PrefixCut := [⟨57,423569571,423569863⟩,
⟨114,835987523,835988095⟩,
⟨128,937754959,937755604⟩]
theorem checked14044 : checkPrefixCuts (2^48) 1844707329 9 Manual.Count131072.C014044.packed 128 cuts14044 = true := by
 decide +kernel
def pointBounds14044 : List (Nat × Nat × Nat) := [(1844765696,95403630204482,95404007651447),(1844824064,95404042622434,95404420069679)]
theorem point_links_checked14044 : (cuts14044.take 2).map (fun c => (1844707329-1+2*2^9*c.k,95403206634911+c.lower,95403584081584+c.upper)) = pointBounds14044 := by
 decide +kernel
def cuts14045 : List PrefixCut := [⟨43,318113602,318113823⟩,
⟨100,729437550,729438059⟩,
⟨128,938908740,938909392⟩]
theorem checked14045 : checkPrefixCuts (2^48) 1844838401 9 Manual.Count131072.C014045.packed 128 cuts14045 = true := by
 decide +kernel
def pointBounds14045 : List (Nat × Nat × Nat) := [(1844882432,95404462503472,95404839951011),(1844940800,95404873827420,95405251275247)]
theorem point_links_checked14045 : (cuts14045.take 2).map (fun c => (1844838401-1+2*2^9*c.k,95404144389870+c.lower,95404521837188+c.upper)) = pointBounds14045 := by
 decide +kernel
def cuts14046 : List PrefixCut := [⟨29,213739662,213739810⟩,
⟨86,630682219,630682650⟩,
⟨128,938231813,938232457⟩]
theorem checked14046 : checkPrefixCuts (2^48) 1844969473 9 Manual.Count131072.C014046.packed 128 cuts14046 = true := by
 decide +kernel
def pointBounds14046 : List (Nat × Nat × Nat) := [(1844999168,95405297038272,95405674486390),(1845057536,95405713980829,95406091429230)]
theorem point_links_checked14046 : (cuts14046.take 2).map (fun c => (1844969473-1+2*2^9*c.k,95405083298610+c.lower,95405460746580+c.upper)) = pointBounds14046 := by
 decide +kernel
def cuts14047 : List PrefixCut := [⟨15,111820585,111820662⟩,
⟨72,527211212,527211578⟩,
⟨128,943198985,943199642⟩]
theorem checked14047 : checkPrefixCuts (2^48) 1845100545 9 Manual.Count131072.C014047.packed 128 cuts14047 = true := by
 decide +kernel
def pointBounds14047 : List (Nat × Nat × Nat) := [(1845115904,95406133351008,95406510799699),(1845174272,95406548741635,95406926190615)]
theorem point_links_checked14047 : (cuts14047.take 2).map (fun c => (1845100545-1+2*2^9*c.k,95406021530423+c.lower,95406398979037+c.upper)) = pointBounds14047 := by
 decide +kernel
def cuts14048 : List PrefixCut := [⟨1,7169461,7169466⟩,
⟨58,431381194,431381496⟩,
⟨115,855579515,855580108⟩,
⟨128,951674341,951675003⟩]
theorem checked14048 : checkPrefixCuts (2^48) 1845231617 9 Manual.Count131072.C014048.packed 128 cuts14048 = true := by
 decide +kernel
def pointBounds14048 : List (Nat × Nat × Nat) := [(1845232640,95406971898869,95407349348145),(1845291008,95407396110602,95407773560175),(1845349376,95407820308923,95408197758787)]
theorem point_links_checked14048 : (cuts14048.take 3).map (fun c => (1845231617-1+2*2^9*c.k,95406964729408+c.lower,95407342178679+c.upper)) = pointBounds14048 := by
 decide +kernel
def cuts14049 : List PrefixCut := [⟨44,320921155,320921374⟩,
⟨101,736551276,736551783⟩,
⟨128,932846112,932846756⟩]
theorem checked14049 : checkPrefixCuts (2^48) 1845362689 9 Manual.Count131072.C014049.packed 128 cuts14049 = true := by
 decide +kernel
def pointBounds14049 : List (Nat × Nat × Nat) := [(1845407744,95408237324904,95408614775056),(1845466112,95408652955025,95409030405465)]
theorem point_links_checked14049 : (cuts14049.take 2).map (fun c => (1845362689-1+2*2^9*c.k,95407916403749+c.lower,95408293853682+c.upper)) = pointBounds14049 := by
 decide +kernel
def cuts14050 : List PrefixCut := [⟨30,222830014,222830167⟩,
⟨87,640874035,640874477⟩,
⟨128,947268626,947269281⟩]
theorem checked14050 : checkPrefixCuts (2^48) 1845493761 9 Manual.Count131072.C014050.packed 128 cuts14050 = true := by
 decide +kernel
def pointBounds14050 : List (Nat × Nat × Nat) := [(1845524480,95409072079875,95409449530605),(1845582848,95409490123896,95409867574915)]
theorem point_links_checked14050 : (cuts14050.take 2).map (fun c => (1845493761-1+2*2^9*c.k,95408849249861+c.lower,95409226700438+c.upper)) = pointBounds14050 := by
 decide +kernel
def cuts14051 : List PrefixCut := [⟨16,112551317,112551396⟩,
⟨73,532398907,532399280⟩,
⟨128,930578360,930579013⟩]
theorem checked14051 : checkPrefixCuts (2^48) 1845624833 9 Manual.Count131072.C014051.packed 128 cuts14051 = true := by
 decide +kernel
def pointBounds14051 : List (Nat × Nat × Nat) := [(1845641216,95409909069804,95410286521115),(1845699584,95410328917394,95410706368999)]
theorem point_links_checked14051 : (cuts14051.take 2).map (fun c => (1845624833-1+2*2^9*c.k,95409796518487+c.lower,95410173969719+c.upper)) = pointBounds14051 := by
 decide +kernel
def cuts14052 : List PrefixCut := [⟨2,14792339,14792349⟩,
⟨59,425006173,425006469⟩,
⟨116,840391764,840392345⟩,
⟨128,926700025,926700667⟩]
theorem checked14052 : checkPrefixCuts (2^48) 1845755905 9 Manual.Count131072.C014052.packed 128 cuts14052 = true := by
 decide +kernel
def pointBounds14052 : List (Nat × Nat × Nat) := [(1845757952,95410741889186,95411119341081),(1845816320,95411152103020,95411529555201),(1845874688,95411567488611,95411944941077)]
theorem point_links_checked14052 : (cuts14052.take 3).map (fun c => (1845755905-1+2*2^9*c.k,95410727096847+c.lower,95411104548732+c.upper)) = pointBounds14052 := by
 decide +kernel
def cuts14053 : List PrefixCut := [⟨45,338213272,338213503⟩,
⟨102,746558432,746558948⟩,
⟨128,932733924,932734568⟩]
theorem checked14053 : checkPrefixCuts (2^48) 1845886977 9 Manual.Count131072.C014053.packed 128 cuts14053 = true := by
 decide +kernel
def pointBounds14053 : List (Nat × Nat × Nat) := [(1845933056,95411992010144,95412369462902),(1845991424,95412400355304,95412777808347)]
theorem point_links_checked14053 : (cuts14053.take 2).map (fun c => (1845886977-1+2*2^9*c.k,95411653796872+c.lower,95412031249399+c.upper)) = pointBounds14053 := by
 decide +kernel
def cuts14054 : List PrefixCut := [⟨31,222309205,222309356⟩,
⟨88,636727222,636727660⟩,
⟨128,925653415,925654055⟩]
theorem checked14054 : checkPrefixCuts (2^48) 1846018049 9 Manual.Count131072.C014054.packed 128 cuts14054 = true := by
 decide +kernel
def pointBounds14054 : List (Nat × Nat × Nat) := [(1846049792,95412808840001,95413186293323),(1846108160,95413223258018,95413600711627)]
theorem point_links_checked14054 : (cuts14054.take 2).map (fun c => (1846018049-1+2*2^9*c.k,95412586530796+c.lower,95412963983967+c.upper)) = pointBounds14054 := by
 decide +kernel
def cuts14055 : List PrefixCut := [⟨17,120600005,120600090⟩,
⟨74,545206962,545207342⟩,
⟨128,940833960,940834609⟩]
theorem checked14055 : checkPrefixCuts (2^48) 1846149121 9 Manual.Count131072.C014055.packed 128 cuts14055 = true := by
 decide +kernel
def pointBounds14055 : List (Nat × Nat × Nat) := [(1846166528,95413632784216,95414010238112),(1846224896,95414057391173,95414434845364)]
theorem point_links_checked14055 : (cuts14055.take 2).map (fun c => (1846149121-1+2*2^9*c.k,95413512184211+c.lower,95413889638022+c.upper)) = pointBounds14055 := by
 decide +kernel
def cuts14056 : List PrefixCut := [⟨3,19514240,19514254⟩,
⟨60,435099646,435099943⟩,
⟨117,847775466,847776047⟩,
⟨128,926436964,926437601⟩]
theorem checked14056 : checkPrefixCuts (2^48) 1846280193 9 Manual.Count131072.C014056.packed 128 cuts14056 = true := by
 decide +kernel
def pointBounds14056 : List (Nat × Nat × Nat) := [(1846283264,95414472532411,95414849986885),(1846341632,95414888117817,95415265572574),(1846400000,95415300793637,95415678248678)]
theorem point_links_checked14056 : (cuts14056.take 3).map (fun c => (1846280193-1+2*2^9*c.k,95414453018171+c.lower,95414830472631+c.upper)) = pointBounds14056 := by
 decide +kernel
def cuts14057 : List PrefixCut := [⟨46,343909946,343910180⟩,
⟨103,759303553,759304076⟩,
⟨128,943139628,943140279⟩]
theorem checked14057 : checkPrefixCuts (2^48) 1846411265 9 Manual.Count131072.C014057.packed 128 cuts14057 = true := by
 decide +kernel
def pointBounds14057 : List (Nat × Nat × Nat) := [(1846458368,95415723365081,95416100820412),(1846516736,95416138758688,95416516214308)]
theorem point_links_checked14057 : (cuts14057.take 2).map (fun c => (1846411265-1+2*2^9*c.k,95415379455135+c.lower,95415756910232+c.upper)) = pointBounds14057 := by
 decide +kernel
def cuts14058 : List PrefixCut := [⟨32,237184417,237184580⟩,
⟨89,645540005,645540451⟩,
⟨128,931792879,931793523⟩]
theorem checked14058 : checkPrefixCuts (2^48) 1846542337 9 Manual.Count131072.C014058.packed 128 cuts14058 = true := by
 decide +kernel
def pointBounds14058 : List (Nat × Nat × Nat) := [(1846575104,95416559779180,95416937235091),(1846633472,95416968134768,95417345590962)]
theorem point_links_checked14058 : (cuts14058.take 2).map (fun c => (1846542337-1+2*2^9*c.k,95416322594763+c.lower,95416700050511+c.upper)) = pointBounds14058 := by
 decide +kernel
def cuts14059 : List PrefixCut := [⟨18,131387674,131387766⟩,
⟨75,555111812,555112201⟩,
⟨128,934013229,934013879⟩]
theorem checked14059 : checkPrefixCuts (2^48) 1846673409 9 Manual.Count131072.C014059.packed 128 cuts14059 = true := by
 decide +kernel
def pointBounds14059 : List (Nat × Nat × Nat) := [(1846691840,95417385775316,95417763231800),(1846750208,95417809499454,95418186956235)]
theorem point_links_checked14059 : (cuts14059.take 2).map (fun c => (1846673409-1+2*2^9*c.k,95417254387642+c.lower,95417631844034+c.upper)) = pointBounds14059 := by
 decide +kernel
def cuts14060 : List PrefixCut := [⟨4,29720276,29720297⟩,
⟨61,442901400,442901711⟩,
⟨118,865213613,865214218⟩,
⟨128,940042721,940043378⟩]
theorem checked14060 : checkPrefixCuts (2^48) 1846804481 9 Manual.Count131072.C014060.packed 128 cuts14060 = true := by
 decide +kernel
def pointBounds14060 : List (Nat × Nat × Nat) := [(1846808576,95418218121147,95418595578210),(1846866944,95418631302271,95419008759624),(1846925312,95419053614484,95419431072131)]
theorem point_links_checked14060 : (cuts14060.take 3).map (fun c => (1846804481-1+2*2^9*c.k,95418188400871+c.lower,95418565857913+c.upper)) = pointBounds14060 := by
 decide +kernel
def cuts14061 : List PrefixCut := [⟨47,348536635,348536879⟩,
⟨104,769907970,769908506⟩,
⟨128,946224642,946225301⟩]
theorem checked14061 : checkPrefixCuts (2^48) 1846935553 9 Manual.Count131072.C014061.packed 128 cuts14061 = true := by
 decide +kernel
def pointBounds14061 : List (Nat × Nat × Nat) := [(1846983680,95419476980227,95419854438170),(1847042048,95419898351562,95420275809797)]
theorem point_links_checked14061 : (cuts14061.take 2).map (fun c => (1846935553-1+2*2^9*c.k,95419128443592+c.lower,95419505901291+c.upper)) = pointBounds14061 := by
 decide +kernel
def cuts14062 : List PrefixCut := [⟨33,238640899,238641066⟩,
⟨90,655566320,655566775⟩,
⟨128,931985461,931986105⟩]
theorem checked14062 : checkPrefixCuts (2^48) 1847066625 9 Manual.Count131072.C014062.packed 128 cuts14062 = true := by
 decide +kernel
def pointBounds14062 : List (Nat × Nat × Nat) := [(1847100416,95420313309133,95420690767658),(1847158784,95420730234554,95421107693367)]
theorem point_links_checked14062 : (cuts14062.take 2).map (fun c => (1847066625-1+2*2^9*c.k,95420074668234+c.lower,95420452126592+c.upper)) = pointBounds14062 := by
 decide +kernel
def cuts14063 : List PrefixCut := [⟨19,137445506,137445604⟩,
⟨76,550078060,550078443⟩,
⟨128,928567073,928567714⟩]
theorem checked14063 : checkPrefixCuts (2^48) 1847197697 9 Manual.Count131072.C014063.packed 128 cuts14063 = true := by
 decide +kernel
def pointBounds14063 : List (Nat × Nat × Nat) := [(1847217152,95421144099201,95421521558301),(1847275520,95421556731755,95421934191140)]
theorem point_links_checked14063 : (cuts14063.take 2).map (fun c => (1847197697-1+2*2^9*c.k,95421006653695+c.lower,95421384112697+c.upper)) = pointBounds14063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000126
