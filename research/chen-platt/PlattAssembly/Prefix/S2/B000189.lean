import PlattAssemblyKernel
import PlattCertificates.Count131072.C016048
import PlattCertificates.Count131072.C016049
import PlattCertificates.Count131072.C016050
import PlattCertificates.Count131072.C016051
import PlattCertificates.Count131072.C016052
import PlattCertificates.Count131072.C016053
import PlattCertificates.Count131072.C016054
import PlattCertificates.Count131072.C016055
import PlattCertificates.Count131072.C016056
import PlattCertificates.Count131072.C016057
import PlattCertificates.Count131072.C016058
import PlattCertificates.Count131072.C016059
import PlattCertificates.Count131072.C016060
import PlattCertificates.Count131072.C016061
import PlattCertificates.Count131072.C016062
import PlattCertificates.Count131072.C016063
import PlattCertificates.Count131072.C016064
import PlattCertificates.Count131072.C016065
import PlattCertificates.Count131072.C016066
import PlattCertificates.Count131072.C016067
import PlattCertificates.Count131072.C016068
import PlattCertificates.Count131072.C016069
import PlattCertificates.Count131072.C016070
import PlattCertificates.Count131072.C016071
import PlattCertificates.Count131072.C016072
import PlattCertificates.Count131072.C016073
import PlattCertificates.Count131072.C016074
import PlattCertificates.Count131072.C016075
import PlattCertificates.Count131072.C016076
import PlattCertificates.Count131072.C016077
import PlattCertificates.Count131072.C016078
import PlattCertificates.Count131072.C016079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16048 : List PrefixCut := [⟨64,404833835,404834100⟩,
⟨128,819805758,819806289⟩]
theorem checked16048 : checkPrefixCuts (2^48) 2107375617 9 Manual.Count131072.C016048.packed 128 cuts16048 = true := by
 decide +kernel
def pointBounds16048 : List (Nat × Nat × Nat) := [(2107441152,97154363453083,97154742066523)]
theorem point_links_checked16048 : (cuts16048.take 1).map (fun c => (2107375617-1+2*2^9*c.k,97153958619248+c.lower,97154337232423+c.upper)) = pointBounds16048 := by
 decide +kernel
def cuts16049 : List PrefixCut := [⟨1,6677910,6677915⟩,
⟨66,418030590,418030857⟩,
⟨128,817885081,817885609⟩]
theorem checked16049 : checkPrefixCuts (2^48) 2107506689 9 Manual.Count131072.C016049.packed 128 cuts16049 = true := by
 decide +kernel
def pointBounds16049 : List (Nat × Nat × Nat) := [(2107507712,97154785102916,97155163716627),(2107574272,97155196455596,97155575069569)]
theorem point_links_checked16049 : (cuts16049.take 2).map (fun c => (2107506689-1+2*2^9*c.k,97154778425006+c.lower,97155157038712+c.upper)) = pointBounds16049 := by
 decide +kernel
def cuts16050 : List PrefixCut := [⟨3,19631826,19631839⟩,
⟨68,427352714,427352993⟩,
⟨128,811824759,811825289⟩]
theorem checked16050 : checkPrefixCuts (2^48) 2107637761 9 Manual.Count131072.C016050.packed 128 cuts16050 = true := by
 decide +kernel
def pointBounds16050 : List (Nat × Nat × Nat) := [(2107640832,97155615941913,97155994556160),(2107707392,97156023662801,97156402277314)]
theorem point_links_checked16050 : (cuts16050.take 2).map (fun c => (2107637761-1+2*2^9*c.k,97155596310087+c.lower,97155974924321+c.upper)) = pointBounds16050 := by
 decide +kernel
def cuts16051 : List PrefixCut := [⟨5,32183494,32183512⟩,
⟨70,438276186,438276469⟩,
⟨128,816314424,816314954⟩]
theorem checked16051 : checkPrefixCuts (2^48) 2107768833 9 Manual.Count131072.C016051.packed 128 cuts16051 = true := by
 decide +kernel
def pointBounds16051 : List (Nat × Nat × Nat) := [(2107773952,97156440318340,97156818933122),(2107840512,97156846411032,97157225026079)]
theorem point_links_checked16051 : (cuts16051.take 2).map (fun c => (2107768833-1+2*2^9*c.k,97156408134846+c.lower,97156786749610+c.upper)) = pointBounds16051 := by
 decide +kernel
def cuts16052 : List PrefixCut := [⟨7,46202456,46202484⟩,
⟨72,457477200,457477488⟩,
⟨128,813192709,813193227⟩]
theorem checked16052 : checkPrefixCuts (2^48) 2107899905 9 Manual.Count131072.C016052.packed 128 cuts16052 = true := by
 decide +kernel
def pointBounds16052 : List (Nat × Nat × Nat) := [(2107907072,97157270651726,97157649267048),(2107973632,97157681926470,97158060542052)]
theorem point_links_checked16052 : (cuts16052.take 2).map (fun c => (2107899905-1+2*2^9*c.k,97157224449270+c.lower,97157603064564+c.upper)) = pointBounds16052 := by
 decide +kernel
def cuts16053 : List PrefixCut := [⟨9,56080384,56080422⟩,
⟨74,468797874,468798174⟩,
⟨128,817815155,817815680⟩]
theorem checked16053 : checkPrefixCuts (2^48) 2108030977 9 Manual.Count131072.C016053.packed 128 cuts16053 = true := by
 decide +kernel
def pointBounds16053 : List (Nat × Nat × Nat) := [(2108040192,97158093722363,97158472338213),(2108106752,97158506439853,97158885055965)]
theorem point_links_checked16053 : (cuts16053.take 2).map (fun c => (2108030977-1+2*2^9*c.k,97158037641979+c.lower,97158416257791+c.upper)) = pointBounds16053 := by
 decide +kernel
def cuts16054 : List PrefixCut := [⟨11,71564774,71564820⟩,
⟨76,478648653,478648960⟩,
⟨128,807350500,807351017⟩]
theorem checked16054 : checkPrefixCuts (2^48) 2108162049 9 Manual.Count131072.C016054.packed 128 cuts16054 = true := by
 decide +kernel
def pointBounds16054 : List (Nat × Nat × Nat) := [(2108173312,97158927021908,97159305638291),(2108239872,97159334105787,97159712722431)]
theorem point_links_checked16054 : (cuts16054.take 2).map (fun c => (2108162049-1+2*2^9*c.k,97158855457134+c.lower,97159234073471+c.upper)) = pointBounds16054 := by
 decide +kernel
def cuts16055 : List PrefixCut := [⟨13,83175480,83175534⟩,
⟨78,499312120,499312436⟩,
⟨128,819983283,819983802⟩]
theorem checked16055 : checkPrefixCuts (2^48) 2108293121 9 Manual.Count131072.C016055.packed 128 cuts16055 = true := by
 decide +kernel
def pointBounds16055 : List (Nat × Nat × Nat) := [(2108306432,97159745983114,97160124600022),(2108372992,97160162119754,97160540736924)]
theorem point_links_checked16055 : (cuts16055.take 2).map (fun c => (2108293121-1+2*2^9*c.k,97159662807634+c.lower,97160041424488+c.upper)) = pointBounds16055 := by
 decide +kernel
def cuts16056 : List PrefixCut := [⟨15,95852730,95852792⟩,
⟨80,513031065,513031390⟩,
⟨128,818864453,818864977⟩]
theorem checked16056 : checkPrefixCuts (2^48) 2108424193 9 Manual.Count131072.C016056.packed 128 cuts16056 = true := by
 decide +kernel
def pointBounds16056 : List (Nat × Nat × Nat) := [(2108439552,97160578643647,97160957261082),(2108506112,97160995821982,97161374439680)]
theorem point_links_checked16056 : (cuts16056.take 2).map (fun c => (2108424193-1+2*2^9*c.k,97160482790917+c.lower,97160861408290+c.upper)) = pointBounds16056 := by
 decide +kernel
def cuts16057 : List PrefixCut := [⟨17,109996797,109996868⟩,
⟨82,531820806,531821148⟩,
⟨128,827623623,827624151⟩]
theorem checked16057 : checkPrefixCuts (2^48) 2108555265 9 Manual.Count131072.C016057.packed 128 cuts16057 = true := by
 decide +kernel
def pointBounds16057 : List (Nat × Nat × Nat) := [(2108572672,97161411652167,97161790270135),(2108639232,97161833476176,97162212094415)]
theorem point_links_checked16057 : (cuts16057.take 2).map (fun c => (2108555265-1+2*2^9*c.k,97161301655370+c.lower,97161680273267+c.upper)) = pointBounds16057 := by
 decide +kernel
def cuts16058 : List PrefixCut := [⟨19,124673038,124673119⟩,
⟨84,532989012,532989357⟩,
⟨128,812489121,812489646⟩]
theorem checked16058 : checkPrefixCuts (2^48) 2108686337 9 Manual.Count131072.C016058.packed 128 cuts16058 = true := by
 decide +kernel
def pointBounds16058 : List (Nat × Nat × Nat) := [(2108705792,97162253952031,97162632570537),(2108772352,97162662268005,97163040886775)]
theorem point_links_checked16058 : (cuts16058.take 2).map (fun c => (2108686337-1+2*2^9*c.k,97162129278993+c.lower,97162507897418+c.upper)) = pointBounds16058 := by
 decide +kernel
def cuts16059 : List PrefixCut := [⟨21,131338963,131339048⟩,
⟨86,540429932,540430282⟩,
⟨128,808834644,808835164⟩]
theorem checked16059 : checkPrefixCuts (2^48) 2108817409 9 Manual.Count131072.C016059.packed 128 cuts16059 = true := by
 decide +kernel
def pointBounds16059 : List (Nat × Nat × Nat) := [(2108838912,97163073107077,97163451726112),(2108905472,97163482198046,97163860817346)]
theorem point_links_checked16059 : (cuts16059.take 2).map (fun c => (2108817409-1+2*2^9*c.k,97162941768114+c.lower,97163320387064+c.upper)) = pointBounds16059 := by
 decide +kernel
def cuts16060 : List PrefixCut := [⟨23,146812802,146812898⟩,
⟨88,556011356,556011719⟩,
⟨128,806248729,806249252⟩]
theorem checked16060 : checkPrefixCuts (2^48) 2108948481 9 Manual.Count131072.C016060.packed 128 cuts16060 = true := by
 decide +kernel
def pointBounds16060 : List (Nat × Nat × Nat) := [(2108972032,97163897415560,97164276035126),(2109038592,97164306614114,97164685233947)]
theorem point_links_checked16060 : (cuts16060.take 2).map (fun c => (2108948481-1+2*2^9*c.k,97163750602758+c.lower,97164129222228+c.upper)) = pointBounds16060 := by
 decide +kernel
def cuts16061 : List PrefixCut := [⟨25,162284737,162284841⟩,
⟨90,574260120,574260494⟩,
⟨128,817942690,817943221⟩]
theorem checked16061 : checkPrefixCuts (2^48) 2109079553 9 Manual.Count131072.C016061.packed 128 cuts16061 = true := by
 decide +kernel
def pointBounds16061 : List (Nat × Nat × Nat) := [(2109105152,97164719136224,97165097756321),(2109171712,97165131111607,97165509731974)]
theorem point_links_checked16061 : (cuts16061.take 2).map (fun c => (2109079553-1+2*2^9*c.k,97164556851487+c.lower,97164935471480+c.upper)) = pointBounds16061 := by
 decide +kernel
def cuts16062 : List PrefixCut := [⟨27,172149820,172149929⟩,
⟨92,585566951,585567324⟩,
⟨128,810418778,810419301⟩]
theorem checked16062 : checkPrefixCuts (2^48) 2109210625 9 Manual.Count131072.C016062.packed 128 cuts16062 = true := by
 decide +kernel
def pointBounds16062 : List (Nat × Nat × Nat) := [(2109238272,97165546943997,97165925564630),(2109304832,97165960361128,97166338982025)]
theorem point_links_checked16062 : (cuts16062.take 2).map (fun c => (2109210625-1+2*2^9*c.k,97165374794177+c.lower,97165753414701+c.upper)) = pointBounds16062 := by
 decide +kernel
def cuts16063 : List PrefixCut := [⟨29,180012075,180012193⟩,
⟨94,598874264,598874653⟩,
⟨128,820509592,820510119⟩]
theorem checked16063 : checkPrefixCuts (2^48) 2109341697 9 Manual.Count131072.C016063.packed 128 cuts16063 = true := by
 decide +kernel
def pointBounds16063 : List (Nat × Nat × Nat) := [(2109371392,97166365225030,97166743846195),(2109437952,97166784087219,97167162708655)]
theorem point_links_checked16063 : (cuts16063.take 2).map (fun c => (2109341697-1+2*2^9*c.k,97166185212955+c.lower,97166563834002+c.upper)) = pointBounds16063 := by
 decide +kernel
def cuts16064 : List PrefixCut := [⟨31,199215075,199215204⟩,
⟨96,604574338,604574732⟩,
⟨128,816989321,816989851⟩]
theorem checked16064 : checkPrefixCuts (2^48) 2109472769 9 Manual.Count131072.C016064.packed 128 cuts16064 = true := by
 decide +kernel
def pointBounds16064 : List (Nat × Nat × Nat) := [(2109504512,97167204937622,97167583559325),(2109571072,97167610296885,97167988918853)]
theorem point_links_checked16064 : (cuts16064.take 2).map (fun c => (2109472769-1+2*2^9*c.k,97167005722547+c.lower,97167384344121+c.upper)) = pointBounds16064 := by
 decide +kernel
def cuts16065 : List PrefixCut := [⟨33,208142067,208142202⟩,
⟨98,624416245,624416648⟩,
⟨128,812535845,812536372⟩]
theorem checked16065 : checkPrefixCuts (2^48) 2109603841 9 Manual.Count131072.C016065.packed 128 cuts16065 = true := by
 decide +kernel
def pointBounds16065 : List (Nat × Nat × Nat) := [(2109637632,97168030853935,97168409476174),(2109704192,97168447128113,97168825750620)]
theorem point_links_checked16065 : (cuts16065.take 2).map (fun c => (2109603841-1+2*2^9*c.k,97167822711868+c.lower,97168201333972+c.upper)) = pointBounds16065 := by
 decide +kernel
def cuts16066 : List PrefixCut := [⟨35,219736238,219736379⟩,
⟨100,635450503,635450909⟩,
⟨128,811151209,811151725⟩]
theorem checked16066 : checkPrefixCuts (2^48) 2109734913 9 Manual.Count131072.C016066.packed 128 cuts16066 = true := by
 decide +kernel
def pointBounds16066 : List (Nat × Nat × Nat) := [(2109770752,97168854983951,97169233606723),(2109837312,97169270698216,97169649321253)]
theorem point_links_checked16066 : (cuts16066.take 2).map (fun c => (2109734913-1+2*2^9*c.k,97168635247713+c.lower,97169013870344+c.upper)) = pointBounds16066 := by
 decide +kernel
def cuts16067 : List PrefixCut := [⟨37,240800840,240800993⟩,
⟨102,659957505,659957923⟩,
⟨128,830177759,830178284⟩]
theorem checked16067 : checkPrefixCuts (2^48) 2109865985 9 Manual.Count131072.C016067.packed 128 cuts16067 = true := by
 decide +kernel
def pointBounds16067 : List (Nat × Nat × Nat) := [(2109903872,97169687199762,97170065823062),(2109970432,97170106356427,97170484979992)]
theorem point_links_checked16067 : (cuts16067.take 2).map (fun c => (2109865985-1+2*2^9*c.k,97169446398922+c.lower,97169825022069+c.upper)) = pointBounds16067 := by
 decide +kernel
def cuts16068 : List PrefixCut := [⟨39,250123740,250123900⟩,
⟨104,670454472,670454898⟩,
⟨128,824656883,824657408⟩]
theorem checked16068 : checkPrefixCuts (2^48) 2109997057 9 Manual.Count131072.C016068.packed 128 cuts16068 = true := by
 decide +kernel
def pointBounds16068 : List (Nat × Nat × Nat) := [(2110036992,97170526700421,97170905324253),(2110103552,97170947031153,97171325655251)]
theorem point_links_checked16068 : (cuts16068.take 2).map (fun c => (2109997057-1+2*2^9*c.k,97170276576681+c.lower,97170655200353+c.upper)) = pointBounds16068 := by
 decide +kernel
def cuts16069 : List PrefixCut := [⟨41,260645963,260646127⟩,
⟨106,669612185,669612615⟩,
⟨128,812600640,812601160⟩]
theorem checked16069 : checkPrefixCuts (2^48) 2110128129 9 Manual.Count131072.C016069.packed 128 cuts16069 = true := by
 decide +kernel
def pointBounds16069 : List (Nat × Nat × Nat) := [(2110170112,97171361879527,97171740503888),(2110236672,97171770845749,97172149470376)]
theorem point_links_checked16069 : (cuts16069.take 2).map (fun c => (2110128129-1+2*2^9*c.k,97171101233564+c.lower,97171479857761+c.upper)) = pointBounds16069 := by
 decide +kernel
def cuts16070 : List PrefixCut := [⟨43,271833791,271833969⟩,
⟨108,686642900,686643343⟩,
⟨128,807882047,807882569⟩]
theorem checked16070 : checkPrefixCuts (2^48) 2110259201 9 Manual.Count131072.C016070.packed 128 cuts16070 = true := by
 decide +kernel
def pointBounds16070 : List (Nat × Nat × Nat) := [(2110303232,97172185667995,97172564292890),(2110369792,97172600477104,97172979102264)]
theorem point_links_checked16070 : (cuts16070.take 2).map (fun c => (2110259201-1+2*2^9*c.k,97171913834204+c.lower,97172292458921+c.upper)) = pointBounds16070 := by
 decide +kernel
def cuts16071 : List PrefixCut := [⟨45,287955117,287955302⟩,
⟨110,699937354,699937804⟩,
⟨128,814367154,814367675⟩]
theorem checked16071 : checkPrefixCuts (2^48) 2110390273 9 Manual.Count131072.C016071.packed 128 cuts16071 = true := by
 decide +kernel
def pointBounds16071 : List (Nat × Nat × Nat) := [(2110436352,97173009671368,97173388296792),(2110502912,97173421653605,97173800279294)]
theorem point_links_checked16071 : (cuts16071.take 2).map (fun c => (2110390273-1+2*2^9*c.k,97172721716251+c.lower,97173100341490+c.upper)) = pointBounds16071 := by
 decide +kernel
def cuts16072 : List PrefixCut := [⟨47,305541428,305541623⟩,
⟨112,722832199,722832660⟩,
⟨128,826852764,826853290⟩]
theorem checked16072 : checkPrefixCuts (2^48) 2110521345 9 Manual.Count131072.C016072.packed 128 cuts16072 = true := by
 decide +kernel
def pointBounds16072 : List (Nat × Nat × Nat) := [(2110569472,97173841624833,97174220250788),(2110636032,97174258915604,97174637541825)]
theorem point_links_checked16072 : (cuts16072.take 2).map (fun c => (2110521345-1+2*2^9*c.k,97173536083405+c.lower,97173914709165+c.upper)) = pointBounds16072 := by
 decide +kernel
def cuts16073 : List PrefixCut := [⟨49,310456536,310456735⟩,
⟨114,721453261,721453721⟩,
⟨128,809865216,809865732⟩]
theorem checked16073 : checkPrefixCuts (2^48) 2110652417 9 Manual.Count131072.C016073.packed 128 cuts16073 = true := by
 decide +kernel
def pointBounds16073 : List (Nat × Nat × Nat) := [(2110702592,97174673392705,97175052019190),(2110769152,97175084389430,97175463016176)]
theorem point_links_checked16073 : (cuts16073.take 2).map (fun c => (2110652417-1+2*2^9*c.k,97174362936169+c.lower,97174741562455+c.upper)) = pointBounds16073 := by
 decide +kernel
def cuts16074 : List PrefixCut := [⟨51,329239321,329239530⟩,
⟨116,738876684,738877157⟩,
⟨128,811815309,811815829⟩]
theorem checked16074 : checkPrefixCuts (2^48) 2110783489 9 Manual.Count131072.C016074.packed 128 cuts16074 = true := by
 decide +kernel
def pointBounds16074 : List (Nat × Nat × Nat) := [(2110835712,97175502040706,97175880667717),(2110902272,97175911678069,97176290305344)]
theorem point_links_checked16074 : (cuts16074.take 2).map (fun c => (2110783489-1+2*2^9*c.k,97175172801385+c.lower,97175551428187+c.upper)) = pointBounds16074 := by
 decide +kernel
def cuts16075 : List PrefixCut := [⟨53,333752270,333752487⟩,
⟨118,749497315,749497801⟩,
⟨128,812297942,812298471⟩]
theorem checked16075 : checkPrefixCuts (2^48) 2110914561 9 Manual.Count131072.C016075.packed 128 cuts16075 = true := by
 decide +kernel
def pointBounds16075 : List (Nat × Nat × Nat) := [(2110968832,97176318368964,97176696996503),(2111035392,97176734114009,97177112741817)]
theorem point_links_checked16075 : (cuts16075.take 2).map (fun c => (2110914561-1+2*2^9*c.k,97175984616694+c.lower,97176363244016+c.upper)) = pointBounds16075 := by
 decide +kernel
def cuts16076 : List PrefixCut := [⟨55,355064610,355064838⟩,
⟨120,765983640,765984134⟩,
⟨128,816247663,816248188⟩]
theorem checked16076 : checkPrefixCuts (2^48) 2111045633 9 Manual.Count131072.C016076.packed 128 cuts16076 = true := by
 decide +kernel
def pointBounds16076 : List (Nat × Nat × Nat) := [(2111101952,97177151979246,97177530607325),(2111168512,97177562898276,97177941526621)]
theorem point_links_checked16076 : (cuts16076.take 2).map (fun c => (2111045633-1+2*2^9*c.k,97176796914636+c.lower,97177175542487+c.upper)) = pointBounds16076 := by
 decide +kernel
def cuts16077 : List PrefixCut := [⟨57,360908694,360908922⟩,
⟨122,778867782,778868278⟩,
⟨128,815930180,815930701⟩]
theorem checked16077 : checkPrefixCuts (2^48) 2111176705 9 Manual.Count131072.C016077.packed 128 cuts16077 = true := by
 decide +kernel
def pointBounds16077 : List (Nat × Nat × Nat) := [(2111235072,97177974070993,97178352699597),(2111301632,97178392030081,97178770658953)]
theorem point_links_checked16077 : (cuts16077.take 2).map (fun c => (2111176705-1+2*2^9*c.k,97177613162299+c.lower,97177991790675+c.upper)) = pointBounds16077 := by
 decide +kernel
def cuts16078 : List PrefixCut := [⟨59,375417510,375417749⟩,
⟨124,790550667,790551169⟩,
⟨128,815212952,815213470⟩]
theorem checked16078 : checkPrefixCuts (2^48) 2111307777 9 Manual.Count131072.C016078.packed 128 cuts16078 = true := by
 decide +kernel
def pointBounds16078 : List (Nat × Nat × Nat) := [(2111368192,97178804509989,97179183139125),(2111434752,97179219643146,97179598272545)]
theorem point_links_checked16078 : (cuts16078.take 2).map (fun c => (2111307777-1+2*2^9*c.k,97178429092479+c.lower,97178807721376+c.upper)) = pointBounds16078 := by
 decide +kernel
def cuts16079 : List PrefixCut := [⟨61,391524302,391524553⟩,
⟨126,800232768,800233285⟩,
⟨128,811563378,811563903⟩]
theorem checked16079 : checkPrefixCuts (2^48) 2111438849 9 Manual.Count131072.C016079.packed 128 cuts16079 = true := by
 decide +kernel
def pointBounds16079 : List (Nat × Nat × Nat) := [(2111501312,97179635829733,97180014459399),(2111567872,97180044538199,97180423168131)]
theorem point_links_checked16079 : (cuts16079.take 2).map (fun c => (2111438849-1+2*2^9*c.k,97179244305431+c.lower,97179622934846+c.upper)) = pointBounds16079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000189
