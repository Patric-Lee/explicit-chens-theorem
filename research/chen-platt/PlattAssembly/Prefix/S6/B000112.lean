import PlattAssemblyKernel
import PlattCertificates.Count131072.C053584
import PlattCertificates.Count131072.C053585
import PlattCertificates.Count131072.C053586
import PlattCertificates.Count131072.C053587
import PlattCertificates.Count131072.C053588
import PlattCertificates.Count131072.C053589
import PlattCertificates.Count131072.C053590
import PlattCertificates.Count131072.C053591
import PlattCertificates.Count131072.C053592
import PlattCertificates.Count131072.C053593
import PlattCertificates.Count131072.C053594
import PlattCertificates.Count131072.C053595
import PlattCertificates.Count131072.C053596
import PlattCertificates.Count131072.C053597
import PlattCertificates.Count131072.C053598
import PlattCertificates.Count131072.C053599
import PlattCertificates.Count131072.C053600
import PlattCertificates.Count131072.C053601
import PlattCertificates.Count131072.C053602
import PlattCertificates.Count131072.C053603
import PlattCertificates.Count131072.C053604
import PlattCertificates.Count131072.C053605
import PlattCertificates.Count131072.C053606
import PlattCertificates.Count131072.C053607
import PlattCertificates.Count131072.C053608
import PlattCertificates.Count131072.C053609
import PlattCertificates.Count131072.C053610
import PlattCertificates.Count131072.C053611
import PlattCertificates.Count131072.C053612
import PlattCertificates.Count131072.C053613
import PlattCertificates.Count131072.C053614
import PlattCertificates.Count131072.C053615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53584 : List PrefixCut := [⟨64,232794690,232794820⟩]
theorem checked53584 : checkPrefixCuts (2^48) 7027294209 10 Manual.Count131072.C053584.packed 64 cuts53584 = true := by
 decide +kernel
def cuts53585 : List PrefixCut := [⟨33,119519879,119519945⟩,
⟨64,229425884,229426013⟩]
theorem checked53585 : checkPrefixCuts (2^48) 7027425281 10 Manual.Count131072.C053585.packed 64 cuts53585 = true := by
 decide +kernel
def pointBounds53585 : List (Nat × Nat × Nat) := [(7027492864,112517432633507,112517820244639)]
theorem point_links_checked53585 : (cuts53585.take 1).map (fun c => (7027425281-1+2*2^10*c.k,112517313113628+c.lower,112517700724694+c.upper)) = pointBounds53585 := by
 decide +kernel
def cuts53586 : List PrefixCut := [⟨64,231544403,231544532⟩]
theorem checked53586 : checkPrefixCuts (2^48) 7027556353 10 Manual.Count131072.C053586.packed 64 cuts53586 = true := by
 decide +kernel
def cuts53587 : List PrefixCut := [⟨13,47461860,47461887⟩,
⟨64,233502608,233502743⟩]
theorem checked53587 : checkPrefixCuts (2^48) 7027687425 10 Manual.Count131072.C053587.packed 64 cuts53587 = true := by
 decide +kernel
def pointBounds53587 : List (Nat × Nat × Nat) := [(7027714048,112517821545775,112518209157126)]
theorem point_links_checked53587 : (cuts53587.take 1).map (fun c => (7027687425-1+2*2^10*c.k,112517774083915+c.lower,112518161695239+c.upper)) = pointBounds53587 := by
 decide +kernel
def cuts53588 : List PrefixCut := [⟨57,208025931,208026048⟩,
⟨64,233017647,233017778⟩]
theorem checked53588 : checkPrefixCuts (2^48) 7027818497 10 Manual.Count131072.C053588.packed 64 cuts53588 = true := by
 decide +kernel
def pointBounds53588 : List (Nat × Nat × Nat) := [(7027935232,112518215612454,112518603224030)]
theorem point_links_checked53588 : (cuts53588.take 1).map (fun c => (7027818497-1+2*2^10*c.k,112518007586523+c.lower,112518395197982+c.upper)) = pointBounds53588 := by
 decide +kernel
def cuts53589 : List PrefixCut := [⟨64,232132184,232132319⟩]
theorem checked53589 : checkPrefixCuts (2^48) 7027949569 10 Manual.Count131072.C053589.packed 64 cuts53589 = true := by
 decide +kernel
def cuts53590 : List PrefixCut := [⟨37,135208199,135208276⟩,
⟨64,233169153,233169287⟩]
theorem checked53590 : checkPrefixCuts (2^48) 7028080641 10 Manual.Count131072.C053590.packed 64 cuts53590 = true := by
 decide +kernel
def pointBounds53590 : List (Nat × Nat × Nat) := [(7028156416,112518607944553,112518995556355)]
theorem point_links_checked53590 : (cuts53590.take 1).map (fun c => (7028080641-1+2*2^10*c.k,112518472736354+c.lower,112518860348079+c.upper)) = pointBounds53590 := by
 decide +kernel
def cuts53591 : List PrefixCut := [⟨64,229199951,229200084⟩]
theorem checked53591 : checkPrefixCuts (2^48) 7028211713 10 Manual.Count131072.C053591.packed 64 cuts53591 = true := by
 decide +kernel
def cuts53592 : List PrefixCut := [⟨17,61994994,61995028⟩,
⟨64,232359491,232359621⟩]
theorem checked53592 : checkPrefixCuts (2^48) 7028342785 10 Manual.Count131072.C053592.packed 64 cuts53592 = true := by
 decide +kernel
def pointBounds53592 : List (Nat × Nat × Nat) := [(7028377600,112518997100452,112519384712478)]
theorem point_links_checked53592 : (cuts53592.take 1).map (fun c => (7028342785-1+2*2^10*c.k,112518935105458+c.lower,112519322717450+c.upper)) = pointBounds53592 := by
 decide +kernel
def cuts53593 : List PrefixCut := [⟨61,223224438,223224561⟩,
⟨64,233556582,233556711⟩]
theorem checked53593 : checkPrefixCuts (2^48) 7028473857 10 Manual.Count131072.C053593.packed 64 cuts53593 = true := by
 decide +kernel
def pointBounds53593 : List (Nat × Nat × Nat) := [(7028598784,112519390689387,112519778301632)]
theorem point_links_checked53593 : (cuts53593.take 1).map (fun c => (7028473857-1+2*2^10*c.k,112519167464949+c.lower,112519555077071+c.upper)) = pointBounds53593 := by
 decide +kernel
def cuts53594 : List PrefixCut := [⟨64,233712397,233712531⟩]
theorem checked53594 : checkPrefixCuts (2^48) 7028604929 10 Manual.Count131072.C053594.packed 64 cuts53594 = true := by
 decide +kernel
def cuts53595 : List PrefixCut := [⟨41,148610943,148611025⟩,
⟨64,231785842,231785971⟩]
theorem checked53595 : checkPrefixCuts (2^48) 7028736001 10 Manual.Count131072.C053595.packed 64 cuts53595 = true := by
 decide +kernel
def pointBounds53595 : List (Nat × Nat × Nat) := [(7028819968,112519783344871,112520170957338)]
theorem point_links_checked53595 : (cuts53595.take 1).map (fun c => (7028736001-1+2*2^10*c.k,112519634733928+c.lower,112520022346313+c.upper)) = pointBounds53595 := by
 decide +kernel
def cuts53596 : List PrefixCut := [⟨64,235065231,235065360⟩]
theorem checked53596 : checkPrefixCuts (2^48) 7028867073 10 Manual.Count131072.C053596.packed 64 cuts53596 = true := by
 decide +kernel
def cuts53597 : List PrefixCut := [⟨21,74242851,74242891⟩,
⟨64,230976295,230976423⟩]
theorem checked53597 : checkPrefixCuts (2^48) 7028998145 10 Manual.Count131072.C053597.packed 64 cuts53597 = true := by
 decide +kernel
def pointBounds53597 : List (Nat × Nat × Nat) := [(7029041152,112520175827852,112520563440535)]
theorem point_links_checked53597 : (cuts53597.take 1).map (fun c => (7028998145-1+2*2^10*c.k,112520101585001+c.lower,112520489197644+c.upper)) = pointBounds53597 := by
 decide +kernel
def cuts53598 : List PrefixCut := [⟨64,234736120,234736256⟩]
theorem checked53598 : checkPrefixCuts (2^48) 7029129217 10 Manual.Count131072.C053598.packed 64 cuts53598 = true := by
 decide +kernel
def cuts53599 : List PrefixCut := [⟨1,4124461,4124463⟩,
⟨64,231688465,231688597⟩]
theorem checked53599 : checkPrefixCuts (2^48) 7029260289 10 Manual.Count131072.C053599.packed 64 cuts53599 = true := by
 decide +kernel
def pointBounds53599 : List (Nat × Nat × Nat) := [(7029262336,112520571421877,112520959034786)]
theorem point_links_checked53599 : (cuts53599.take 1).map (fun c => (7029260289-1+2*2^10*c.k,112520567297416+c.lower,112520954910323+c.upper)) = pointBounds53599 := by
 decide +kernel
def cuts53600 : List PrefixCut := [⟨45,165374737,165374833⟩,
⟨64,234366987,234367122⟩]
theorem checked53600 : checkPrefixCuts (2^48) 7029391361 10 Manual.Count131072.C053600.packed 64 cuts53600 = true := by
 decide +kernel
def pointBounds53600 : List (Nat × Nat × Nat) := [(7029483520,112520964360618,112521351973753)]
theorem point_links_checked53600 : (cuts53600.take 1).map (fun c => (7029391361-1+2*2^10*c.k,112520798985881+c.lower,112521186598920+c.upper)) = pointBounds53600 := by
 decide +kernel
def cuts53601 : List PrefixCut := [⟨64,231519686,231519819⟩]
theorem checked53601 : checkPrefixCuts (2^48) 7029522433 10 Manual.Count131072.C053601.packed 64 cuts53601 = true := by
 decide +kernel
def cuts53602 : List PrefixCut := [⟨25,90412427,90412480⟩,
⟨64,231915761,231915894⟩]
theorem checked53602 : checkPrefixCuts (2^48) 7029653505 10 Manual.Count131072.C053602.packed 64 cuts53602 = true := by
 decide +kernel
def pointBounds53602 : List (Nat × Nat × Nat) := [(7029704704,112521355284981,112521742898341)]
theorem point_links_checked53602 : (cuts53602.take 1).map (fun c => (7029653505-1+2*2^10*c.k,112521264872554+c.lower,112521652485861+c.upper)) = pointBounds53602 := by
 decide +kernel
def cuts53603 : List PrefixCut := [⟨64,229428944,229429077⟩]
theorem checked53603 : checkPrefixCuts (2^48) 7029784577 10 Manual.Count131072.C053603.packed 64 cuts53603 = true := by
 decide +kernel
def cuts53604 : List PrefixCut := [⟨5,17617406,17617415⟩,
⟨64,228183452,228183581⟩]
theorem checked53604 : checkPrefixCuts (2^48) 7029915649 10 Manual.Count131072.C053604.packed 64 cuts53604 = true := by
 decide +kernel
def pointBounds53604 : List (Nat × Nat × Nat) := [(7029925888,112521743834665,112522131448247)]
theorem point_links_checked53604 : (cuts53604.take 1).map (fun c => (7029915649-1+2*2^10*c.k,112521726217259+c.lower,112522113830832+c.upper)) = pointBounds53604 := by
 decide +kernel
def cuts53605 : List PrefixCut := [⟨49,173807354,173807452⟩,
⟨64,226497597,226497725⟩]
theorem checked53605 : checkPrefixCuts (2^48) 7030046721 10 Manual.Count131072.C053605.packed 64 cuts53605 = true := by
 decide +kernel
def pointBounds53605 : List (Nat × Nat × Nat) := [(7030147072,112522128208065,112522515821865)]
theorem point_links_checked53605 : (cuts53605.take 1).map (fun c => (7030046721-1+2*2^10*c.k,112521954400711+c.lower,112522342014413+c.upper)) = pointBounds53605 := by
 decide +kernel
def cuts53606 : List PrefixCut := [⟨64,233379847,233379979⟩]
theorem checked53606 : checkPrefixCuts (2^48) 7030177793 10 Manual.Count131072.C053606.packed 64 cuts53606 = true := by
 decide +kernel
def cuts53607 : List PrefixCut := [⟨29,103335950,103336007⟩,
⟨64,230773090,230773225⟩]
theorem checked53607 : checkPrefixCuts (2^48) 7030308865 10 Manual.Count131072.C053607.packed 64 cuts53607 = true := by
 decide +kernel
def pointBounds53607 : List (Nat × Nat × Nat) := [(7030368256,112522517614105,112522905228124)]
theorem point_links_checked53607 : (cuts53607.take 1).map (fun c => (7030308865-1+2*2^10*c.k,112522414278155+c.lower,112522801892117+c.upper)) = pointBounds53607 := by
 decide +kernel
def cuts53608 : List PrefixCut := [⟨64,231209201,231209337⟩]
theorem checked53608 : checkPrefixCuts (2^48) 7030439937 10 Manual.Count131072.C053608.packed 64 cuts53608 = true := by
 decide +kernel
def cuts53609 : List PrefixCut := [⟨9,32709247,32709266⟩,
⟨64,230724474,230724603⟩]
theorem checked53609 : checkPrefixCuts (2^48) 7030571009 10 Manual.Count131072.C053609.packed 64 cuts53609 = true := by
 decide +kernel
def pointBounds53609 : List (Nat × Nat × Nat) := [(7030589440,112522908969693,112523296583945)]
theorem point_links_checked53609 : (cuts53609.take 1).map (fun c => (7030571009-1+2*2^10*c.k,112522876260446+c.lower,112523263874679+c.upper)) = pointBounds53609 := by
 decide +kernel
def cuts53610 : List PrefixCut := [⟨53,192086955,192087064⟩,
⟨64,231921207,231921337⟩]
theorem checked53610 : checkPrefixCuts (2^48) 7030702081 10 Manual.Count131072.C053610.packed 64 cuts53610 = true := by
 decide +kernel
def pointBounds53610 : List (Nat × Nat × Nat) := [(7030810624,112523299071875,112523686686346)]
theorem point_links_checked53610 : (cuts53610.take 1).map (fun c => (7030702081-1+2*2^10*c.k,112523106984920+c.lower,112523494599282+c.upper)) = pointBounds53610 := by
 decide +kernel
def cuts53611 : List PrefixCut := [⟨64,228513983,228514114⟩]
theorem checked53611 : checkPrefixCuts (2^48) 7030833153 10 Manual.Count131072.C053611.packed 64 cuts53611 = true := by
 decide +kernel
def cuts53612 : List PrefixCut := [⟨33,121181157,121181230⟩,
⟨64,235115212,235115348⟩]
theorem checked53612 : checkPrefixCuts (2^48) 7030964225 10 Manual.Count131072.C053612.packed 64 cuts53612 = true := by
 decide +kernel
def pointBounds53612 : List (Nat × Nat × Nat) := [(7031031808,112523688601267,112524076215963)]
theorem point_links_checked53612 : (cuts53612.take 1).map (fun c => (7030964225-1+2*2^10*c.k,112523567420110+c.lower,112523955034733+c.upper)) = pointBounds53612 := by
 decide +kernel
def cuts53613 : List PrefixCut := [⟨64,233469476,233469609⟩]
theorem checked53613 : checkPrefixCuts (2^48) 7031095297 10 Manual.Count131072.C053613.packed 64 cuts53613 = true := by
 decide +kernel
def cuts53614 : List PrefixCut := [⟨13,46517240,46517266⟩,
⟨64,230062450,230062580⟩]
theorem checked53614 : checkPrefixCuts (2^48) 7031226369 10 Manual.Count131072.C053614.packed 64 cuts53614 = true := by
 decide +kernel
def pointBounds53614 : List (Nat × Nat × Nat) := [(7031252992,112524082522038,112524470136956)]
theorem point_links_checked53614 : (cuts53614.take 1).map (fun c => (7031226369-1+2*2^10*c.k,112524036004798+c.lower,112524423619690+c.upper)) = pointBounds53614 := by
 decide +kernel
def cuts53615 : List PrefixCut := [⟨57,206239921,206240037⟩,
⟨64,232500040,232500170⟩]
theorem checked53615 : checkPrefixCuts (2^48) 7031357441 10 Manual.Count131072.C053615.packed 64 cuts53615 = true := by
 decide +kernel
def pointBounds53615 : List (Nat × Nat × Nat) := [(7031474176,112524472307169,112524859922307)]
theorem point_links_checked53615 : (cuts53615.take 1).map (fun c => (7031357441-1+2*2^10*c.k,112524266067248+c.lower,112524653682270+c.upper)) = pointBounds53615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000112
