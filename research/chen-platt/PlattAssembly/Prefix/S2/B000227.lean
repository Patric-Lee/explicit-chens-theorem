import PlattAssemblyKernel
import PlattCertificates.Count131072.C017264
import PlattCertificates.Count131072.C017265
import PlattCertificates.Count131072.C017266
import PlattCertificates.Count131072.C017267
import PlattCertificates.Count131072.C017268
import PlattCertificates.Count131072.C017269
import PlattCertificates.Count131072.C017270
import PlattCertificates.Count131072.C017271
import PlattCertificates.Count131072.C017272
import PlattCertificates.Count131072.C017273
import PlattCertificates.Count131072.C017274
import PlattCertificates.Count131072.C017275
import PlattCertificates.Count131072.C017276
import PlattCertificates.Count131072.C017277
import PlattCertificates.Count131072.C017278
import PlattCertificates.Count131072.C017279
import PlattCertificates.Count131072.C017280
import PlattCertificates.Count131072.C017281
import PlattCertificates.Count131072.C017282
import PlattCertificates.Count131072.C017283
import PlattCertificates.Count131072.C017284
import PlattCertificates.Count131072.C017285
import PlattCertificates.Count131072.C017286
import PlattCertificates.Count131072.C017287
import PlattCertificates.Count131072.C017288
import PlattCertificates.Count131072.C017289
import PlattCertificates.Count131072.C017290
import PlattCertificates.Count131072.C017291
import PlattCertificates.Count131072.C017292
import PlattCertificates.Count131072.C017293
import PlattCertificates.Count131072.C017294
import PlattCertificates.Count131072.C017295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000227
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17264 : List PrefixCut := [⟨64,379597595,379597834⟩,
⟨128,757073310,757073788⟩]
theorem checked17264 : checkPrefixCuts (2^48) 2266759169 9 Manual.Count131072.C017264.packed 128 cuts17264 = true := by
 decide +kernel
def pointBounds17264 : List (Nat × Nat × Nat) := [(2266824704,98108576360615,98108955576366)]
theorem point_links_checked17264 : (cuts17264.take 1).map (fun c => (2266759169-1+2*2^9*c.k,98108196763020+c.lower,98108575978532+c.upper)) = pointBounds17264 := by
 decide +kernel
def cuts17265 : List PrefixCut := [⟨6,35263621,35263643⟩,
⟨76,446624093,446624373⟩,
⟨128,762740910,762741384⟩]
theorem checked17265 : checkPrefixCuts (2^48) 2266890241 9 Manual.Count131072.C017265.packed 128 cuts17265 = true := by
 decide +kernel
def pointBounds17265 : List (Nat × Nat × Nat) := [(2266896384,98108989099951,98109368315963),(2266968064,98109400460423,98109779676693)]
theorem point_links_checked17265 : (cuts17265.take 2).map (fun c => (2266890241-1+2*2^9*c.k,98108953836330+c.lower,98109333052320+c.upper)) = pointBounds17265 := by
 decide +kernel
def cuts17266 : List PrefixCut := [⟨18,103177091,103177155⟩,
⟨88,516125625,516125946⟩,
⟨128,755247412,755247881⟩]
theorem checked17266 : checkPrefixCuts (2^48) 2267021313 9 Manual.Count131072.C017266.packed 128 cuts17266 = true := by
 decide +kernel
def pointBounds17266 : List (Nat × Nat × Nat) := [(2267039744,98109819754331,98110198970859),(2267111424,98110232702865,98110611919650)]
theorem point_links_checked17266 : (cuts17266.take 2).map (fun c => (2267021313-1+2*2^9*c.k,98109716577240+c.lower,98110095793704+c.upper)) = pointBounds17266 := by
 decide +kernel
def cuts17267 : List PrefixCut := [⟨30,177910762,177910873⟩,
⟨100,586239595,586239963⟩,
⟨128,751355248,751355722⟩]
theorem checked17267 : checkPrefixCuts (2^48) 2267152385 9 Manual.Count131072.C017267.packed 128 cuts17267 = true := by
 decide +kernel
def pointBounds17267 : List (Nat × Nat × Nat) := [(2267183104,98110649735414,98111028952458),(2267254784,98111058064247,98111437281548)]
theorem point_links_checked17267 : (cuts17267.take 2).map (fun c => (2267152385-1+2*2^9*c.k,98110471824652+c.lower,98110851041585+c.upper)) = pointBounds17267 := by
 decide +kernel
def cuts17268 : List PrefixCut := [⟨42,243821089,243821245⟩,
⟨112,661683061,661683481⟩,
⟨128,757642976,757643455⟩]
theorem checked17268 : checkPrefixCuts (2^48) 2267283457 9 Manual.Count131072.C017268.packed 128 cuts17268 = true := by
 decide +kernel
def pointBounds17268 : List (Nat × Nat × Nat) := [(2267326464,98111467000989,98111846218552),(2267398144,98111884862961,98112264080788)]
theorem point_links_checked17268 : (cuts17268.take 2).map (fun c => (2267283457-1+2*2^9*c.k,98111223179900+c.lower,98111602397307+c.upper)) = pointBounds17268 := by
 decide +kernel
def cuts17269 : List PrefixCut := [⟨54,319654406,319654600⟩,
⟨124,740345118,740345571⟩,
⟨128,764923268,764923736⟩]
theorem checked17269 : checkPrefixCuts (2^48) 2267414529 9 Manual.Count131072.C017269.packed 128 cuts17269 = true := by
 decide +kernel
def pointBounds17269 : List (Nat × Nat × Nat) := [(2267469824,98112300477282,98112679695362),(2267541504,98112721167994,98113100386333)]
theorem point_links_checked17269 : (cuts17269.take 2).map (fun c => (2267414529-1+2*2^9*c.k,98111980822876+c.lower,98112360040762+c.upper)) = pointBounds17269 := by
 decide +kernel
def cuts17270 : List PrefixCut := [⟨66,379589826,379590063⟩,
⟨128,752838330,752838800⟩]
theorem checked17270 : checkPrefixCuts (2^48) 2267545601 9 Manual.Count131072.C017270.packed 128 cuts17270 = true := by
 decide +kernel
def pointBounds17270 : List (Nat × Nat × Nat) := [(2267613184,98113125335970,98113504554561)]
theorem point_links_checked17270 : (cuts17270.take 1).map (fun c => (2267545601-1+2*2^9*c.k,98112745746144+c.lower,98113124964498+c.upper)) = pointBounds17270 := by
 decide +kernel
def cuts17271 : List PrefixCut := [⟨8,49525699,49525728⟩,
⟨78,464466878,464467164⟩,
⟨128,761235440,761235908⟩]
theorem checked17271 : checkPrefixCuts (2^48) 2267676673 9 Manual.Count131072.C017271.packed 128 cuts17271 = true := by
 decide +kernel
def pointBounds17271 : List (Nat × Nat × Nat) := [(2267684864,98113548110173,98113927329026),(2267756544,98113963051352,98114342270462)]
theorem point_links_checked17271 : (cuts17271.take 2).map (fun c => (2267676673-1+2*2^9*c.k,98113498584474+c.lower,98113877803298+c.upper)) = pointBounds17271 := by
 decide +kernel
def cuts17272 : List PrefixCut := [⟨20,118159437,118159513⟩,
⟨90,538287155,538287495⟩,
⟨128,761067289,761067764⟩]
theorem checked17272 : checkPrefixCuts (2^48) 2267807745 9 Manual.Count131072.C017272.packed 128 cuts17272 = true := by
 decide +kernel
def pointBounds17272 : List (Nat × Nat × Nat) := [(2267828224,98114377979351,98114757198719),(2267899904,98114798107069,98115177326701)]
theorem point_links_checked17272 : (cuts17272.take 2).map (fun c => (2267807745-1+2*2^9*c.k,98114259819914+c.lower,98114639039206+c.upper)) = pointBounds17272 := by
 decide +kernel
def cuts17273 : List PrefixCut := [⟨32,186412525,186412640⟩,
⟨102,597950333,597950701⟩,
⟨128,753080334,753080799⟩]
theorem checked17273 : checkPrefixCuts (2^48) 2267938817 9 Manual.Count131072.C017273.packed 128 cuts17273 = true := by
 decide +kernel
def pointBounds17273 : List (Nat × Nat × Nat) := [(2267971584,98115207299728,98115586519610),(2268043264,98115618837536,98115998057671)]
theorem point_links_checked17273 : (cuts17273.take 2).map (fun c => (2267938817-1+2*2^9*c.k,98115020887203+c.lower,98115400106970+c.upper)) = pointBounds17273 := by
 decide +kernel
def cuts17274 : List PrefixCut := [⟨44,259000959,259001119⟩,
⟨114,677586414,677586830⟩,
⟨128,757256353,757256819⟩]
theorem checked17274 : checkPrefixCuts (2^48) 2268069889 9 Manual.Count131072.C017274.packed 128 cuts17274 = true := by
 decide +kernel
def pointBounds17274 : List (Nat × Nat × Nat) := [(2268114944,98116032968496,98116412188888),(2268186624,98116451553951,98116830774599)]
theorem point_links_checked17274 : (cuts17274.take 2).map (fun c => (2268069889-1+2*2^9*c.k,98115773967537+c.lower,98116153187769+c.upper)) = pointBounds17274 := by
 decide +kernel
def cuts17275 : List PrefixCut := [⟨56,327361355,327361560⟩,
⟨126,738722985,738723451⟩,
⟨128,750263260,750263734⟩]
theorem checked17275 : checkPrefixCuts (2^48) 2268200961 9 Manual.Count131072.C017275.packed 128 cuts17275 = true := by
 decide +kernel
def pointBounds17275 : List (Nat × Nat × Nat) := [(2268258304,98116858585245,98117237806148),(2268329984,98117269946875,98117649168039)]
theorem point_links_checked17275 : (cuts17275.take 2).map (fun c => (2268200961-1+2*2^9*c.k,98116531223890+c.lower,98116910444588+c.upper)) = pointBounds17275 := by
 decide +kernel
def cuts17276 : List PrefixCut := [⟨68,396954350,396954592⟩,
⟨128,759650268,759650737⟩]
theorem checked17276 : checkPrefixCuts (2^48) 2268332033 9 Manual.Count131072.C017276.packed 128 cuts17276 = true := by
 decide +kernel
def pointBounds17276 : List (Nat × Nat × Nat) := [(2268401664,98117678441500,98118057662914)]
theorem point_links_checked17276 : (cuts17276.take 1).map (fun c => (2268332033-1+2*2^9*c.k,98117281487150+c.lower,98117660708322+c.upper)) = pointBounds17276 := by
 decide +kernel
def cuts17277 : List PrefixCut := [⟨10,56953397,56953433⟩,
⟨80,463685107,463685406⟩,
⟨128,741615210,741615687⟩]
theorem checked17277 : checkPrefixCuts (2^48) 2268463105 9 Manual.Count131072.C017277.packed 128 cuts17277 = true := by
 decide +kernel
def pointBounds17277 : List (Nat × Nat × Nat) := [(2268473344,98118098090815,98118477312492),(2268545024,98118504822525,98118884044465)]
theorem point_links_checked17277 : (cuts17277.take 2).map (fun c => (2268463105-1+2*2^9*c.k,98118041137418+c.lower,98118420359059+c.upper)) = pointBounds17277 := by
 decide +kernel
def cuts17278 : List PrefixCut := [⟨22,135364712,135364795⟩,
⟨92,541202204,541202542⟩,
⟨128,746659528,746659994⟩]
theorem checked17278 : checkPrefixCuts (2^48) 2268594177 9 Manual.Count131072.C017278.packed 128 cuts17278 = true := by
 decide +kernel
def pointBounds17278 : List (Nat × Nat × Nat) := [(2268616704,98118918117340,98119297339541),(2268688384,98119323954832,98119703177288)]
theorem point_links_checked17278 : (cuts17278.take 2).map (fun c => (2268594177-1+2*2^9*c.k,98118782752628+c.lower,98119161974746+c.upper)) = pointBounds17278 := by
 decide +kernel
def cuts17279 : List PrefixCut := [⟨34,200863615,200863743⟩,
⟨104,613126699,613127087⟩,
⟨128,757161429,757161909⟩]
theorem checked17279 : checkPrefixCuts (2^48) 2268725249 9 Manual.Count131072.C017279.packed 128 cuts17279 = true := by
 decide +kernel
def pointBounds17279 : List (Nat × Nat × Nat) := [(2268760064,98119730275771,98120109498483),(2268831744,98120142538855,98120521761827)]
theorem point_links_checked17279 : (cuts17279.take 2).map (fun c => (2268725249-1+2*2^9*c.k,98119529412156+c.lower,98119908634740+c.upper)) = pointBounds17279 := by
 decide +kernel
def cuts17280 : List PrefixCut := [⟨46,267471132,267471300⟩,
⟨116,680824780,680825200⟩,
⟨128,754140361,754140826⟩]
theorem checked17280 : checkPrefixCuts (2^48) 2268856321 9 Manual.Count131072.C017280.packed 128 cuts17280 = true := by
 decide +kernel
def pointBounds17280 : List (Nat × Nat × Nat) := [(2268903424,98120554044717,98120933267949),(2268975104,98120967398365,98121346621849)]
theorem point_links_checked17280 : (cuts17280.take 2).map (fun c => (2268856321-1+2*2^9*c.k,98120286573585+c.lower,98120665796649+c.upper)) = pointBounds17280 := by
 decide +kernel
def cuts17281 : List PrefixCut := [⟨58,337916185,337916395⟩,
⟨128,756453766,756454235⟩]
theorem checked17281 : checkPrefixCuts (2^48) 2268987393 9 Manual.Count131072.C017281.packed 128 cuts17281 = true := by
 decide +kernel
def pointBounds17281 : List (Nat × Nat × Nat) := [(2269046784,98121378630131,98121757853870),(2269118464,98121797167712,98122176391710)]
theorem point_links_checked17281 : (cuts17281.take 2).map (fun c => (2268987393-1+2*2^9*c.k,98121040713946+c.lower,98121419937475+c.upper)) = pointBounds17281 := by
 decide +kernel
def cuts17282 : List PrefixCut := [⟨70,421377340,421377597⟩,
⟨128,761372011,761372480⟩]
theorem checked17282 : checkPrefixCuts (2^48) 2269118465 9 Manual.Count131072.C017282.packed 128 cuts17282 = true := by
 decide +kernel
def pointBounds17282 : List (Nat × Nat × Nat) := [(2269190144,98122218545052,98122597769307)]
theorem point_links_checked17282 : (cuts17282.take 1).map (fun c => (2269118465-1+2*2^9*c.k,98121797167712+c.lower,98122176391710+c.upper)) = pointBounds17282 := by
 decide +kernel
def cuts17283 : List PrefixCut := [⟨12,71446132,71446176⟩,
⟨82,476796124,476796423⟩,
⟨128,744211031,744211496⟩]
theorem checked17283 : checkPrefixCuts (2^48) 2269249537 9 Manual.Count131072.C017283.packed 128 cuts17283 = true := by
 decide +kernel
def pointBounds17283 : List (Nat × Nat × Nat) := [(2269261824,98122629985855,98123009210366),(2269333504,98123035335847,98123414560613)]
theorem point_links_checked17283 : (cuts17283.take 2).map (fun c => (2269249537-1+2*2^9*c.k,98122558539723+c.lower,98122937764190+c.upper)) = pointBounds17283 := by
 decide +kernel
def cuts17284 : List PrefixCut := [⟨24,142511537,142511627⟩,
⟨94,562719332,562719676⟩,
⟨128,761780098,761780565⟩]
theorem checked17284 : checkPrefixCuts (2^48) 2269380609 9 Manual.Count131072.C017284.packed 128 cuts17284 = true := by
 decide +kernel
def pointBounds17284 : List (Nat × Nat × Nat) := [(2269405184,98123445262291,98123824487313),(2269476864,98123865470086,98124244695362)]
theorem point_links_checked17284 : (cuts17284.take 2).map (fun c => (2269380609-1+2*2^9*c.k,98123302750754+c.lower,98123681975686+c.upper)) = pointBounds17284 := by
 decide +kernel
def cuts17285 : List PrefixCut := [⟨36,208235296,208235427⟩,
⟨106,622711656,622712041⟩,
⟨128,756154906,756155374⟩]
theorem checked17285 : checkPrefixCuts (2^48) 2269511681 9 Manual.Count131072.C017285.packed 128 cuts17285 = true := by
 decide +kernel
def pointBounds17285 : List (Nat × Nat × Nat) := [(2269548544,98124272766148,98124651991678),(2269620224,98124687242508,98125066468292)]
theorem point_links_checked17285 : (cuts17285.take 2).map (fun c => (2269511681-1+2*2^9*c.k,98124064530852+c.lower,98124443756251+c.upper)) = pointBounds17285 := by
 decide +kernel
def cuts17286 : List PrefixCut := [⟨48,288709088,288709264⟩,
⟨118,710476037,710476469⟩,
⟨128,766404718,766405183⟩]
theorem checked17286 : checkPrefixCuts (2^48) 2269642753 9 Manual.Count131072.C017286.packed 128 cuts17286 = true := by
 decide +kernel
def pointBounds17286 : List (Nat × Nat × Nat) := [(2269691904,98125109394846,98125488620889),(2269763584,98125531161795,98125910388094)]
theorem point_links_checked17286 : (cuts17286.take 2).map (fun c => (2269642753-1+2*2^9*c.k,98124820685758+c.lower,98125199911625+c.upper)) = pointBounds17286 := by
 decide +kernel
def cuts17287 : List PrefixCut := [⟨60,352307908,352308130⟩,
⟨128,751231441,751231915⟩]
theorem checked17287 : checkPrefixCuts (2^48) 2269773825 9 Manual.Count131072.C017287.packed 128 cuts17287 = true := by
 decide +kernel
def pointBounds17287 : List (Nat × Nat × Nat) := [(2269835264,98125939398384,98126318624938)]
theorem point_links_checked17287 : (cuts17287.take 1).map (fun c => (2269773825-1+2*2^9*c.k,98125587090476+c.lower,98125966316808+c.upper)) = pointBounds17287 := by
 decide +kernel
def cuts17288 : List PrefixCut := [⟨2,12028280,12028288⟩,
⟨72,426067177,426067446⟩,
⟨128,755900150,755900627⟩]
theorem checked17288 : checkPrefixCuts (2^48) 2269904897 9 Manual.Count131072.C017288.packed 128 cuts17288 = true := by
 decide +kernel
def pointBounds17288 : List (Nat × Nat × Nat) := [(2269906944,98126350350197,98126729577011),(2269978624,98126764389094,98127143616169)]
theorem point_links_checked17288 : (cuts17288.take 2).map (fun c => (2269904897-1+2*2^9*c.k,98126338321917+c.lower,98126717548723+c.upper)) = pointBounds17288 := by
 decide +kernel
def cuts17289 : List PrefixCut := [⟨14,82084947,82084996⟩,
⟨84,491757998,491758300⟩,
⟨128,754988459,754988923⟩]
theorem checked17289 : checkPrefixCuts (2^48) 2270035969 9 Manual.Count131072.C017289.packed 128 cuts17289 = true := by
 decide +kernel
def pointBounds17289 : List (Nat × Nat × Nat) := [(2270050304,98127176307014,98127555534346),(2270121984,98127585980065,98127965207650)]
theorem point_links_checked17289 : (cuts17289.take 2).map (fun c => (2270035969-1+2*2^9*c.k,98127094222067+c.lower,98127473449350+c.upper)) = pointBounds17289 := by
 decide +kernel
def cuts17290 : List PrefixCut := [⟨26,151637199,151637294⟩,
⟨96,563764111,563764466⟩,
⟨128,751225462,751225932⟩]
theorem checked17290 : checkPrefixCuts (2^48) 2270167041 9 Manual.Count131072.C017290.packed 128 cuts17290 = true := by
 decide +kernel
def pointBounds17290 : List (Nat × Nat × Nat) := [(2270193664,98128000847725,98128380075567),(2270265344,98128412974637,98128792202739)]
theorem point_links_checked17290 : (cuts17290.take 2).map (fun c => (2270167041-1+2*2^9*c.k,98127849210526+c.lower,98128228438273+c.upper)) = pointBounds17290 := by
 decide +kernel
def cuts17291 : List PrefixCut := [⟨38,223536668,223536806⟩,
⟨108,640472636,640473034⟩,
⟨128,759240549,759241019⟩]
theorem checked17291 : checkPrefixCuts (2^48) 2270298113 9 Manual.Count131072.C017291.packed 128 cuts17291 = true := by
 decide +kernel
def pointBounds17291 : List (Nat × Nat × Nat) := [(2270337024,98128823972656,98129203201011),(2270408704,98129240908624,98129620137239)]
theorem point_links_checked17291 : (cuts17291.take 2).map (fun c => (2270298113-1+2*2^9*c.k,98128600435988+c.lower,98128979664205+c.upper)) = pointBounds17291 := by
 decide +kernel
def cuts17292 : List PrefixCut := [⟨50,294311692,294311873⟩,
⟨120,708617954,708618390⟩,
⟨128,754485886,754486349⟩]
theorem checked17292 : checkPrefixCuts (2^48) 2270429185 9 Manual.Count131072.C017292.packed 128 cuts17292 = true := by
 decide +kernel
def pointBounds17292 : List (Nat × Nat × Nat) := [(2270480384,98129653988229,98130033217097),(2270552064,98130068294491,98130447523614)]
theorem point_links_checked17292 : (cuts17292.take 2).map (fun c => (2270429185-1+2*2^9*c.k,98129359676537+c.lower,98129738905224+c.upper)) = pointBounds17292 := by
 decide +kernel
def cuts17293 : List PrefixCut := [⟨62,372020175,372020403⟩,
⟨128,763863588,763864062⟩]
theorem checked17293 : checkPrefixCuts (2^48) 2270560257 9 Manual.Count131072.C017293.packed 128 cuts17293 = true := by
 decide +kernel
def pointBounds17293 : List (Nat × Nat × Nat) := [(2270623744,98130486182598,98130865411976)]
theorem point_links_checked17293 : (cuts17293.take 1).map (fun c => (2270560257-1+2*2^9*c.k,98130114162423+c.lower,98130493391573+c.upper)) = pointBounds17293 := by
 decide +kernel
def cuts17294 : List PrefixCut := [⟨4,24420097,24420112⟩,
⟨74,436331949,436332223⟩,
⟨128,755638340,755638813⟩]
theorem checked17294 : checkPrefixCuts (2^48) 2270691329 9 Manual.Count131072.C017294.packed 128 cuts17294 = true := by
 decide +kernel
def pointBounds17294 : List (Nat × Nat × Nat) := [(2270695424,98130902446108,98131281675747),(2270767104,98131314357960,98131693587858)]
theorem point_links_checked17294 : (cuts17294.take 2).map (fun c => (2270691329-1+2*2^9*c.k,98130878026011+c.lower,98131257255635+c.upper)) = pointBounds17294 := by
 decide +kernel
def cuts17295 : List PrefixCut := [⟨16,94451721,94451780⟩,
⟨86,507329121,507329437⟩,
⟨128,756710175,756710643⟩]
theorem checked17295 : checkPrefixCuts (2^48) 2270822401 9 Manual.Count131072.C017295.packed 128 cuts17295 = true := by
 decide +kernel
def pointBounds17295 : List (Nat × Nat × Nat) := [(2270838784,98131728116072,98132107346228),(2270910464,98132140993472,98132520223885)]
theorem point_links_checked17295 : (cuts17295.take 2).map (fun c => (2270822401-1+2*2^9*c.k,98131633664351+c.lower,98132012894448+c.upper)) = pointBounds17295 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000227
