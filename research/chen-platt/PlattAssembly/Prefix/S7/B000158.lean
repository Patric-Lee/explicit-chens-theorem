import PlattAssemblyKernel
import PlattCertificates.Count131072.C065056
import PlattCertificates.Count131072.C065057
import PlattCertificates.Count131072.C065058
import PlattCertificates.Count131072.C065059
import PlattCertificates.Count131072.C065060
import PlattCertificates.Count131072.C065061
import PlattCertificates.Count131072.C065062
import PlattCertificates.Count131072.C065063
import PlattCertificates.Count131072.C065064
import PlattCertificates.Count131072.C065065
import PlattCertificates.Count131072.C065066
import PlattCertificates.Count131072.C065067
import PlattCertificates.Count131072.C065068
import PlattCertificates.Count131072.C065069
import PlattCertificates.Count131072.C065070
import PlattCertificates.Count131072.C065071
import PlattCertificates.Count131072.C065072
import PlattCertificates.Count131072.C065073
import PlattCertificates.Count131072.C065074
import PlattCertificates.Count131072.C065075
import PlattCertificates.Count131072.C065076
import PlattCertificates.Count131072.C065077
import PlattCertificates.Count131072.C065078
import PlattCertificates.Count131072.C065079
import PlattCertificates.Count131072.C065080
import PlattCertificates.Count131072.C065081
import PlattCertificates.Count131072.C065082
import PlattCertificates.Count131072.C065083
import PlattCertificates.Count131072.C065084
import PlattCertificates.Count131072.C065085
import PlattCertificates.Count131072.C065086
import PlattCertificates.Count131072.C065087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65056 : List PrefixCut := [⟨18,55001787,55001821⟩,
⟨64,191168936,191169048⟩]
theorem checked65056 : checkPrefixCuts (2^48) 8530952193 10 Manual.Count131072.C065056.packed 64 cuts65056 = true := by
 decide +kernel
def pointBounds65056 : List (Nat × Nat × Nat) := [(8530989056,114914046689413,114914435669618)]
theorem point_links_checked65056 : (cuts65056.take 1).map (fun c => (8530952193-1+2*2^10*c.k,114913991687626+c.lower,114914380667797+c.upper)) = pointBounds65056 := by
 decide +kernel
def cuts65057 : List PrefixCut := [⟨64,190209182,190209282⟩]
theorem checked65057 : checkPrefixCuts (2^48) 8531083265 10 Manual.Count131072.C065057.packed 64 cuts65057 = true := by
 decide +kernel
def cuts65058 : List PrefixCut := [⟨21,62489591,62489627⟩,
⟨64,190668162,190668273⟩]
theorem checked65058 : checkPrefixCuts (2^48) 8531214337 10 Manual.Count131072.C065058.packed 64 cuts65058 = true := by
 decide +kernel
def pointBounds65058 : List (Nat × Nat × Nat) := [(8531257344,114914435555335,114914824535754)]
theorem point_links_checked65058 : (cuts65058.take 1).map (fun c => (8531214337-1+2*2^10*c.k,114914373065744+c.lower,114914762046127+c.upper)) = pointBounds65058 := by
 decide +kernel
def cuts65059 : List PrefixCut := [⟨64,187398945,187399053⟩]
theorem checked65059 : checkPrefixCuts (2^48) 8531345409 10 Manual.Count131072.C065059.packed 64 cuts65059 = true := by
 decide +kernel
def cuts65060 : List PrefixCut := [⟨24,70306855,70306893⟩,
⟨64,188187878,188187987⟩]
theorem checked65060 : checkPrefixCuts (2^48) 8531476481 10 Manual.Count131072.C065060.packed 64 cuts65060 = true := by
 decide +kernel
def pointBounds65060 : List (Nat × Nat × Nat) := [(8531525632,114914821439706,114915210420346)]
theorem point_links_checked65060 : (cuts65060.take 1).map (fun c => (8531476481-1+2*2^10*c.k,114914751132851+c.lower,114915140113453+c.upper)) = pointBounds65060 := by
 decide +kernel
def cuts65061 : List PrefixCut := [⟨64,188844841,188844950⟩]
theorem checked65061 : checkPrefixCuts (2^48) 8531607553 10 Manual.Count131072.C065061.packed 64 cuts65061 = true := by
 decide +kernel
def cuts65062 : List PrefixCut := [⟨27,80499013,80499060⟩,
⟨64,189831665,189831779⟩]
theorem checked65062 : checkPrefixCuts (2^48) 8531738625 10 Manual.Count131072.C065062.packed 64 cuts65062 = true := by
 decide +kernel
def pointBounds65062 : List (Nat × Nat × Nat) := [(8531793920,114915208664583,114915597645450)]
theorem point_links_checked65062 : (cuts65062.take 1).map (fun c => (8531738625-1+2*2^10*c.k,114915128165570+c.lower,114915517146390+c.upper)) = pointBounds65062 := by
 decide +kernel
def cuts65063 : List PrefixCut := [⟨64,187354448,187354560⟩]
theorem checked65063 : checkPrefixCuts (2^48) 8531869697 10 Manual.Count131072.C065063.packed 64 cuts65063 = true := by
 decide +kernel
def cuts65064 : List PrefixCut := [⟨30,89436900,89436950⟩,
⟨64,189957789,189957897⟩]
theorem checked65064 : checkPrefixCuts (2^48) 8532000769 10 Manual.Count131072.C065064.packed 64 cuts65064 = true := by
 decide +kernel
def pointBounds65064 : List (Nat × Nat × Nat) := [(8532062208,114915594788583,114915983769679)]
theorem point_links_checked65064 : (cuts65064.take 1).map (fun c => (8532000769-1+2*2^10*c.k,114915505351683+c.lower,114915894332729+c.upper)) = pointBounds65064 := by
 decide +kernel
def cuts65065 : List PrefixCut := [⟨64,188635277,188635392⟩]
theorem checked65065 : checkPrefixCuts (2^48) 8532131841 10 Manual.Count131072.C065065.packed 64 cuts65065 = true := by
 decide +kernel
def cuts65066 : List PrefixCut := [⟨33,97516511,97516569⟩,
⟨64,190380812,190380921⟩]
theorem checked65066 : checkPrefixCuts (2^48) 8532262913 10 Manual.Count131072.C065066.packed 64 cuts65066 = true := by
 decide +kernel
def pointBounds65066 : List (Nat × Nat × Nat) := [(8532330496,114915981461260,114916370442587)]
theorem point_links_checked65066 : (cuts65066.take 1).map (fun c => (8532262913-1+2*2^10*c.k,114915883944749+c.lower,114916272926018+c.upper)) = pointBounds65066 := by
 decide +kernel
def cuts65067 : List PrefixCut := [⟨64,193016980,193017087⟩]
theorem checked65067 : checkPrefixCuts (2^48) 8532393985 10 Manual.Count131072.C065067.packed 64 cuts65067 = true := by
 decide +kernel
def cuts65068 : List PrefixCut := [⟨36,107541927,107541991⟩,
⟨64,189913135,189913248⟩]
theorem checked65068 : checkPrefixCuts (2^48) 8532525057 10 Manual.Count131072.C065068.packed 64 cuts65068 = true := by
 decide +kernel
def pointBounds65068 : List (Nat × Nat × Nat) := [(8532598784,114916374884468,114916763866017)]
theorem point_links_checked65068 : (cuts65068.take 1).map (fun c => (8532525057-1+2*2^10*c.k,114916267342541+c.lower,114916656324026+c.upper)) = pointBounds65068 := by
 decide +kernel
def cuts65069 : List PrefixCut := [⟨64,189184480,189184594⟩]
theorem checked65069 : checkPrefixCuts (2^48) 8532656129 10 Manual.Count131072.C065069.packed 64 cuts65069 = true := by
 decide +kernel
def cuts65070 : List PrefixCut := [⟨39,116148271,116148339⟩,
⟨64,189280546,189280657⟩]
theorem checked65070 : checkPrefixCuts (2^48) 8532787201 10 Manual.Count131072.C065070.packed 64 cuts65070 = true := by
 decide +kernel
def pointBounds65070 : List (Nat × Nat × Nat) := [(8532867072,114916762588427,114917151570207)]
theorem point_links_checked65070 : (cuts65070.take 1).map (fun c => (8532787201-1+2*2^10*c.k,114916646440156+c.lower,114917035421868+c.upper)) = pointBounds65070 := by
 decide +kernel
def cuts65071 : List PrefixCut := [⟨64,188782817,188782924⟩]
theorem checked65071 : checkPrefixCuts (2^48) 8532918273 10 Manual.Count131072.C065071.packed 64 cuts65071 = true := by
 decide +kernel
def cuts65072 : List PrefixCut := [⟨42,122576976,122577047⟩,
⟨64,188186166,188186273⟩]
theorem checked65072 : checkPrefixCuts (2^48) 8533049345 10 Manual.Count131072.C065072.packed 64 cuts65072 = true := by
 decide +kernel
def pointBounds65072 : List (Nat × Nat × Nat) := [(8533135360,114917147080495,114917536062496)]
theorem point_links_checked65072 : (cuts65072.take 1).map (fun c => (8533049345-1+2*2^10*c.k,114917024503519+c.lower,114917413485449+c.upper)) = pointBounds65072 := by
 decide +kernel
def cuts65073 : List PrefixCut := [⟨64,190558250,190558363⟩]
theorem checked65073 : checkPrefixCuts (2^48) 8533180417 10 Manual.Count131072.C065073.packed 64 cuts65073 = true := by
 decide +kernel
def cuts65074 : List PrefixCut := [⟨45,134249942,134250019⟩,
⟨64,189136971,189137079⟩]
theorem checked65074 : checkPrefixCuts (2^48) 8533311489 10 Manual.Count131072.C065074.packed 64 cuts65074 = true := by
 decide +kernel
def pointBounds65074 : List (Nat × Nat × Nat) := [(8533403648,114917537497877,114917926480104)]
theorem point_links_checked65074 : (cuts65074.take 1).map (fun c => (8533311489-1+2*2^10*c.k,114917403247935+c.lower,114917792230085+c.upper)) = pointBounds65074 := by
 decide +kernel
def cuts65075 : List PrefixCut := [⟨64,190750314,190750425⟩]
theorem checked65075 : checkPrefixCuts (2^48) 8533442561 10 Manual.Count131072.C065075.packed 64 cuts65075 = true := by
 decide +kernel
def cuts65076 : List PrefixCut := [⟨48,143118534,143118613⟩,
⟨64,189329074,189329179⟩]
theorem checked65076 : checkPrefixCuts (2^48) 8533573633 10 Manual.Count131072.C065076.packed 64 cuts65076 = true := by
 decide +kernel
def pointBounds65076 : List (Nat × Nat × Nat) := [(8533671936,114917926253754,114918315236202)]
theorem point_links_checked65076 : (cuts65076.take 1).map (fun c => (8533573633-1+2*2^10*c.k,114917783135220+c.lower,114918172117589+c.upper)) = pointBounds65076 := by
 decide +kernel
def cuts65077 : List PrefixCut := [⟨64,189820894,189821006⟩]
theorem checked65077 : checkPrefixCuts (2^48) 8533704705 10 Manual.Count131072.C065077.packed 64 cuts65077 = true := by
 decide +kernel
def cuts65078 : List PrefixCut := [⟨51,148721222,148721310⟩,
⟨64,187871976,187872089⟩]
theorem checked65078 : checkPrefixCuts (2^48) 8533835777 10 Manual.Count131072.C065078.packed 64 cuts65078 = true := by
 decide +kernel
def pointBounds65078 : List (Nat × Nat × Nat) := [(8533940224,114918311006410,114918699989084)]
theorem point_links_checked65078 : (cuts65078.take 1).map (fun c => (8533835777-1+2*2^10*c.k,114918162285188+c.lower,114918551267774+c.upper)) = pointBounds65078 := by
 decide +kernel
def cuts65079 : List PrefixCut := [⟨64,187704194,187704300⟩]
theorem checked65079 : checkPrefixCuts (2^48) 8533966849 10 Manual.Count131072.C065079.packed 64 cuts65079 = true := by
 decide +kernel
def cuts65080 : List PrefixCut := [⟨54,159237919,159238011⟩,
⟨64,188624807,188624918⟩]
theorem checked65080 : checkPrefixCuts (2^48) 8534097921 10 Manual.Count131072.C065080.packed 64 cuts65080 = true := by
 decide +kernel
def pointBounds65080 : List (Nat × Nat × Nat) := [(8534208512,114918697099277,114919086082174)]
theorem point_links_checked65080 : (cuts65080.take 1).map (fun c => (8534097921-1+2*2^10*c.k,114918537861358+c.lower,114918926844163+c.upper)) = pointBounds65080 := by
 decide +kernel
def cuts65081 : List PrefixCut := [⟨64,188226127,188226239⟩]
theorem checked65081 : checkPrefixCuts (2^48) 8534228993 10 Manual.Count131072.C065081.packed 64 cuts65081 = true := by
 decide +kernel
def cuts65082 : List PrefixCut := [⟨57,171238098,171238198⟩,
⟨64,192016060,192016172⟩]
theorem checked65082 : checkPrefixCuts (2^48) 8534360065 10 Manual.Count131072.C065082.packed 64 cuts65082 = true := by
 decide +kernel
def pointBounds65082 : List (Nat × Nat × Nat) := [(8534476800,114919085950390,114919474933518)]
theorem point_links_checked65082 : (cuts65082.take 1).map (fun c => (8534360065-1+2*2^10*c.k,114918914712292+c.lower,114919303695320+c.upper)) = pointBounds65082 := by
 decide +kernel
def cuts65083 : List PrefixCut := [⟨64,187395827,187395935⟩]
theorem checked65083 : checkPrefixCuts (2^48) 8534491137 10 Manual.Count131072.C065083.packed 64 cuts65083 = true := by
 decide +kernel
def cuts65084 : List PrefixCut := [⟨60,178323503,178323607⟩,
⟨64,190559033,190559145⟩]
theorem checked65084 : checkPrefixCuts (2^48) 8534622209 10 Manual.Count131072.C065084.packed 64 cuts65084 = true := by
 decide +kernel
def pointBounds65084 : List (Nat × Nat × Nat) := [(8534745088,114919472447682,114919861431034)]
theorem point_links_checked65084 : (cuts65084.take 1).map (fun c => (8534622209-1+2*2^10*c.k,114919294124179+c.lower,114919683107427+c.upper)) = pointBounds65084 := by
 decide +kernel
def cuts65085 : List PrefixCut := [⟨64,190589078,190589194⟩]
theorem checked65085 : checkPrefixCuts (2^48) 8534753281 10 Manual.Count131072.C065085.packed 64 cuts65085 = true := by
 decide +kernel
def cuts65086 : List PrefixCut := [⟨63,185936148,185936259⟩,
⟨64,188739350,188739462⟩]
theorem checked65086 : checkPrefixCuts (2^48) 8534884353 10 Manual.Count131072.C065086.packed 64 cuts65086 = true := by
 decide +kernel
def pointBounds65086 : List (Nat × Nat × Nat) := [(8535013376,114919861208438,114920250192025)]
theorem point_links_checked65086 : (cuts65086.take 1).map (fun c => (8534884353-1+2*2^10*c.k,114919675272290+c.lower,114920064255766+c.upper)) = pointBounds65086 := by
 decide +kernel
def cuts65087 : List PrefixCut := [⟨64,186329004,186329111⟩]
theorem checked65087 : checkPrefixCuts (2^48) 8535015425 10 Manual.Count131072.C065087.packed 64 cuts65087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000158
