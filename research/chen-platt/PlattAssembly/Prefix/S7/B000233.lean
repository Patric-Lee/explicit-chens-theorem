import PlattAssemblyKernel
import PlattCertificates.Count131072.C067456
import PlattCertificates.Count131072.C067457
import PlattCertificates.Count131072.C067458
import PlattCertificates.Count131072.C067459
import PlattCertificates.Count131072.C067460
import PlattCertificates.Count131072.C067461
import PlattCertificates.Count131072.C067462
import PlattCertificates.Count131072.C067463
import PlattCertificates.Count131072.C067464
import PlattCertificates.Count131072.C067465
import PlattCertificates.Count131072.C067466
import PlattCertificates.Count131072.C067467
import PlattCertificates.Count131072.C067468
import PlattCertificates.Count131072.C067469
import PlattCertificates.Count131072.C067470
import PlattCertificates.Count131072.C067471
import PlattCertificates.Count131072.C067472
import PlattCertificates.Count131072.C067473
import PlattCertificates.Count131072.C067474
import PlattCertificates.Count131072.C067475
import PlattCertificates.Count131072.C067476
import PlattCertificates.Count131072.C067477
import PlattCertificates.Count131072.C067478
import PlattCertificates.Count131072.C067479
import PlattCertificates.Count131072.C067480
import PlattCertificates.Count131072.C067481
import PlattCertificates.Count131072.C067482
import PlattCertificates.Count131072.C067483
import PlattCertificates.Count131072.C067484
import PlattCertificates.Count131072.C067485
import PlattCertificates.Count131072.C067486
import PlattCertificates.Count131072.C067487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000233
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67456 : List PrefixCut := [⟨64,180392843,180392948⟩]
theorem checked67456 : checkPrefixCuts (2^48) 8845524993 10 Manual.Count131072.C067456.packed 64 cuts67456 = true := by
 decide +kernel
def cuts67457 : List PrefixCut := [⟨20,57372574,57372607⟩,
⟨64,179721944,179722048⟩]
theorem checked67457 : checkPrefixCuts (2^48) 8845656065 10 Manual.Count131072.C067457.packed 64 cuts67457 = true := by
 decide +kernel
def pointBounds67457 : List (Nat × Nat × Nat) := [(8845697024,115359609155381,115359998394410)]
theorem point_links_checked67457 : (cuts67457.take 1).map (fun c => (8845656065-1+2*2^10*c.k,115359551782807+c.lower,115359941021803+c.upper)) = pointBounds67457 := by
 decide +kernel
def cuts67458 : List PrefixCut := [⟨64,182964917,182965024⟩]
theorem checked67458 : checkPrefixCuts (2^48) 8845787137 10 Manual.Count131072.C067458.packed 64 cuts67458 = true := by
 decide +kernel
def cuts67459 : List PrefixCut := [⟨27,77099007,77099050⟩,
⟨64,182739464,182739567⟩]
theorem checked67459 : checkPrefixCuts (2^48) 8845918209 10 Manual.Count131072.C067459.packed 64 cuts67459 = true := by
 decide +kernel
def pointBounds67459 : List (Nat × Nat × Nat) := [(8845973504,115359991568675,115360380807925)]
theorem point_links_checked67459 : (cuts67459.take 1).map (fun c => (8845918209-1+2*2^10*c.k,115359914469668+c.lower,115360303708875+c.upper)) = pointBounds67459 := by
 decide +kernel
def cuts67460 : List PrefixCut := [⟨64,182832206,182832315⟩]
theorem checked67460 : checkPrefixCuts (2^48) 8846049281 10 Manual.Count131072.C067460.packed 64 cuts67460 = true := by
 decide +kernel
def cuts67461 : List PrefixCut := [⟨34,95042395,95042453⟩,
⟨64,183243122,183243234⟩]
theorem checked67461 : checkPrefixCuts (2^48) 8846180353 10 Manual.Count131072.C067461.packed 64 cuts67461 = true := by
 decide +kernel
def pointBounds67461 : List (Nat × Nat × Nat) := [(8846249984,115360375083733,115360764323210)]
theorem point_links_checked67461 : (cuts67461.take 1).map (fun c => (8846180353-1+2*2^10*c.k,115360280041338+c.lower,115360669280757+c.upper)) = pointBounds67461 := by
 decide +kernel
def cuts67462 : List PrefixCut := [⟨64,183590435,183590540⟩]
theorem checked67462 : checkPrefixCuts (2^48) 8846311425 10 Manual.Count131072.C067462.packed 64 cuts67462 = true := by
 decide +kernel
def cuts67463 : List PrefixCut := [⟨41,116389186,116389253⟩,
⟨64,182092274,182092380⟩]
theorem checked67463 : checkPrefixCuts (2^48) 8846442497 10 Manual.Count131072.C067463.packed 64 cuts67463 = true := by
 decide +kernel
def pointBounds67463 : List (Nat × Nat × Nat) := [(8846526464,115360763264081,115361152503784)]
theorem point_links_checked67463 : (cuts67463.take 1).map (fun c => (8846442497-1+2*2^10*c.k,115360646874895+c.lower,115361036114531+c.upper)) = pointBounds67463 := by
 decide +kernel
def cuts67464 : List PrefixCut := [⟨64,183775890,183775998⟩]
theorem checked67464 : checkPrefixCuts (2^48) 8846573569 10 Manual.Count131072.C067464.packed 64 cuts67464 = true := by
 decide +kernel
def cuts67465 : List PrefixCut := [⟨48,134457554,134457633⟩,
⟨64,179509729,179509836⟩]
theorem checked67465 : checkPrefixCuts (2^48) 8846704641 10 Manual.Count131072.C067465.packed 64 cuts67465 = true := by
 decide +kernel
def pointBounds67465 : List (Nat × Nat × Nat) := [(8846802944,115361147200613,115361536440542)]
theorem point_links_checked67465 : (cuts67465.take 1).map (fun c => (8846704641-1+2*2^10*c.k,115361012743059+c.lower,115361401982909+c.upper)) = pointBounds67465 := by
 decide +kernel
def cuts67466 : List PrefixCut := [⟨64,181543297,181543405⟩]
theorem checked67466 : checkPrefixCuts (2^48) 8846835713 10 Manual.Count131072.C067466.packed 64 cuts67466 = true := by
 decide +kernel
def cuts67467 : List PrefixCut := [⟨55,158378924,158379013⟩,
⟨64,184435851,184435956⟩]
theorem checked67467 : checkPrefixCuts (2^48) 8846966785 10 Manual.Count131072.C067467.packed 64 cuts67467 = true := by
 decide +kernel
def pointBounds67467 : List (Nat × Nat × Nat) := [(8847079424,115361532175009,115361921415163)]
theorem point_links_checked67467 : (cuts67467.take 1).map (fun c => (8846966785-1+2*2^10*c.k,115361373796085+c.lower,115361763036150+c.upper)) = pointBounds67467 := by
 decide +kernel
def cuts67468 : List PrefixCut := [⟨64,183510478,183510580⟩]
theorem checked67468 : checkPrefixCuts (2^48) 8847097857 10 Manual.Count131072.C067468.packed 64 cuts67468 = true := by
 decide +kernel
def cuts67469 : List PrefixCut := [⟨62,177081209,177081314⟩,
⟨64,182298799,182298907⟩]
theorem checked67469 : checkPrefixCuts (2^48) 8847228929 10 Manual.Count131072.C067469.packed 64 cuts67469 = true := by
 decide +kernel
def pointBounds67469 : List (Nat × Nat × Nat) := [(8847355904,115361918823623,115362308064000)]
theorem point_links_checked67469 : (cuts67469.take 1).map (fun c => (8847228929-1+2*2^10*c.k,115361741742414+c.lower,115362130982686+c.upper)) = pointBounds67469 := by
 decide +kernel
def cuts67470 : List PrefixCut := [⟨64,180514493,180514599⟩]
theorem checked67470 : checkPrefixCuts (2^48) 8847360001 10 Manual.Count131072.C067470.packed 64 cuts67470 = true := by
 decide +kernel
def cuts67471 : List PrefixCut := [⟨64,180798149,180798249⟩]
theorem checked67471 : checkPrefixCuts (2^48) 8847491073 10 Manual.Count131072.C067471.packed 64 cuts67471 = true := by
 decide +kernel
def cuts67472 : List PrefixCut := [⟨5,14093427,14093433⟩,
⟨64,180986340,180986440⟩]
theorem checked67472 : checkPrefixCuts (2^48) 8847622145 10 Manual.Count131072.C067472.packed 64 cuts67472 = true := by
 decide +kernel
def pointBounds67472 : List (Nat × Nat × Nat) := [(8847632384,115362299447282,115362688687874)]
theorem point_links_checked67472 : (cuts67472.take 1).map (fun c => (8847622145-1+2*2^10*c.k,115362285353855+c.lower,115362674594441+c.upper)) = pointBounds67472 := by
 decide +kernel
def cuts67473 : List PrefixCut := [⟨64,180951859,180951962⟩]
theorem checked67473 : checkPrefixCuts (2^48) 8847753217 10 Manual.Count131072.C067473.packed 64 cuts67473 = true := by
 decide +kernel
def cuts67474 : List PrefixCut := [⟨13,36043710,36043732⟩,
⟨64,181935357,181935470⟩]
theorem checked67474 : checkPrefixCuts (2^48) 8847884289 10 Manual.Count131072.C067474.packed 64 cuts67474 = true := by
 decide +kernel
def pointBounds67474 : List (Nat × Nat × Nat) := [(8847910912,115362683335764,115363072576575)]
theorem point_links_checked67474 : (cuts67474.take 1).map (fun c => (8847884289-1+2*2^10*c.k,115362647292054+c.lower,115363036532843+c.upper)) = pointBounds67474 := by
 decide +kernel
def cuts67475 : List PrefixCut := [⟨64,181328225,181328333⟩]
theorem checked67475 : checkPrefixCuts (2^48) 8848015361 10 Manual.Count131072.C067475.packed 64 cuts67475 = true := by
 decide +kernel
def cuts67476 : List PrefixCut := [⟨21,59805915,59805951⟩,
⟨64,181770908,181771014⟩]
theorem checked67476 : checkPrefixCuts (2^48) 8848146433 10 Manual.Count131072.C067476.packed 64 cuts67476 = true := by
 decide +kernel
def pointBounds67476 : List (Nat × Nat × Nat) := [(8848189440,115363070361551,115363459602597)]
theorem point_links_checked67476 : (cuts67476.take 1).map (fun c => (8848146433-1+2*2^10*c.k,115363010555636+c.lower,115363399796646+c.upper)) = pointBounds67476 := by
 decide +kernel
def cuts67477 : List PrefixCut := [⟨64,184408528,184408629⟩]
theorem checked67477 : checkPrefixCuts (2^48) 8848277505 10 Manual.Count131072.C067477.packed 64 cuts67477 = true := by
 decide +kernel
def cuts67478 : List PrefixCut := [⟨29,83025889,83025939⟩,
⟨64,182051828,182051931⟩]
theorem checked67478 : checkPrefixCuts (2^48) 8848408577 10 Manual.Count131072.C067478.packed 64 cuts67478 = true := by
 decide +kernel
def pointBounds67478 : List (Nat × Nat × Nat) := [(8848467968,115363459760961,115363849002228)]
theorem point_links_checked67478 : (cuts67478.take 1).map (fun c => (8848408577-1+2*2^10*c.k,115363376735072+c.lower,115363765976289+c.upper)) = pointBounds67478 := by
 decide +kernel
def cuts67479 : List PrefixCut := [⟨64,181794640,181794752⟩]
theorem checked67479 : checkPrefixCuts (2^48) 8848539649 10 Manual.Count131072.C067479.packed 64 cuts67479 = true := by
 decide +kernel
def cuts67480 : List PrefixCut := [⟨37,105989963,105990024⟩,
⟨64,182841664,182841769⟩]
theorem checked67480 : checkPrefixCuts (2^48) 8848670721 10 Manual.Count131072.C067480.packed 64 cuts67480 = true := by
 decide +kernel
def pointBounds67480 : List (Nat × Nat × Nat) := [(8848746496,115363846571503,115364235812996)]
theorem point_links_checked67480 : (cuts67480.take 1).map (fun c => (8848670721-1+2*2^10*c.k,115363740581540+c.lower,115364129822972+c.upper)) = pointBounds67480 := by
 decide +kernel
def cuts67481 : List PrefixCut := [⟨64,182807156,182807260⟩]
theorem checked67481 : checkPrefixCuts (2^48) 8848801793 10 Manual.Count131072.C067481.packed 64 cuts67481 = true := by
 decide +kernel
def cuts67482 : List PrefixCut := [⟨45,128729974,128730045⟩,
⟨64,182613585,182613689⟩]
theorem checked67482 : checkPrefixCuts (2^48) 8848932865 10 Manual.Count131072.C067482.packed 64 cuts67482 = true := by
 decide +kernel
def pointBounds67482 : List (Nat × Nat × Nat) := [(8849025024,115364234960334,115364624202046)]
theorem point_links_checked67482 : (cuts67482.take 1).map (fun c => (8848932865-1+2*2^10*c.k,115364106230360+c.lower,115364495472001+c.upper)) = pointBounds67482 := by
 decide +kernel
def cuts67483 : List PrefixCut := [⟨64,179589101,179589207⟩]
theorem checked67483 : checkPrefixCuts (2^48) 8849063937 10 Manual.Count131072.C067483.packed 64 cuts67483 = true := by
 decide +kernel
def cuts67484 : List PrefixCut := [⟨53,150577993,150578075⟩,
⟨64,182131070,182131169⟩]
theorem checked67484 : checkPrefixCuts (2^48) 8849195009 10 Manual.Count131072.C067484.packed 64 cuts67484 = true := by
 decide +kernel
def pointBounds67484 : List (Nat × Nat × Nat) := [(8849303552,115364619011039,115365008252972)]
theorem point_links_checked67484 : (cuts67484.take 1).map (fun c => (8849195009-1+2*2^10*c.k,115364468433046+c.lower,115364857674897+c.upper)) = pointBounds67484 := by
 decide +kernel
def cuts67485 : List PrefixCut := [⟨64,181969323,181969430⟩]
theorem checked67485 : checkPrefixCuts (2^48) 8849326081 10 Manual.Count131072.C067485.packed 64 cuts67485 = true := by
 decide +kernel
def cuts67486 : List PrefixCut := [⟨61,172933569,172933668⟩,
⟨64,182157472,182157577⟩]
theorem checked67486 : checkPrefixCuts (2^48) 8849457153 10 Manual.Count131072.C067486.packed 64 cuts67486 = true := by
 decide +kernel
def pointBounds67486 : List (Nat × Nat × Nat) := [(8849582080,115365005467008,115365394709164)]
theorem point_links_checked67486 : (cuts67486.take 1).map (fun c => (8849457153-1+2*2^10*c.k,115364832533439+c.lower,115365221775496+c.upper)) = pointBounds67486 := by
 decide +kernel
def cuts67487 : List PrefixCut := [⟨64,183267996,183268102⟩]
theorem checked67487 : checkPrefixCuts (2^48) 8849588225 10 Manual.Count131072.C067487.packed 64 cuts67487 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000233
