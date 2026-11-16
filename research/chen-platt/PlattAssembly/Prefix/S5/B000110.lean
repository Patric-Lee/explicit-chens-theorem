import PlattAssemblyKernel
import PlattCertificates.Count131072.C043520
import PlattCertificates.Count131072.C043521
import PlattCertificates.Count131072.C043522
import PlattCertificates.Count131072.C043523
import PlattCertificates.Count131072.C043524
import PlattCertificates.Count131072.C043525
import PlattCertificates.Count131072.C043526
import PlattCertificates.Count131072.C043527
import PlattCertificates.Count131072.C043528
import PlattCertificates.Count131072.C043529
import PlattCertificates.Count131072.C043530
import PlattCertificates.Count131072.C043531
import PlattCertificates.Count131072.C043532
import PlattCertificates.Count131072.C043533
import PlattCertificates.Count131072.C043534
import PlattCertificates.Count131072.C043535
import PlattCertificates.Count131072.C043536
import PlattCertificates.Count131072.C043537
import PlattCertificates.Count131072.C043538
import PlattCertificates.Count131072.C043539
import PlattCertificates.Count131072.C043540
import PlattCertificates.Count131072.C043541
import PlattCertificates.Count131072.C043542
import PlattCertificates.Count131072.C043543
import PlattCertificates.Count131072.C043544
import PlattCertificates.Count131072.C043545
import PlattCertificates.Count131072.C043546
import PlattCertificates.Count131072.C043547
import PlattCertificates.Count131072.C043548
import PlattCertificates.Count131072.C043549
import PlattCertificates.Count131072.C043550
import PlattCertificates.Count131072.C043551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43520 : List PrefixCut := [⟨38,172290575,172290678⟩,
⟨64,287034585,287034755⟩]
theorem checked43520 : checkPrefixCuts (2^48) 5708185601 10 Manual.Count131072.C043520.packed 64 cuts43520 = true := by
 decide +kernel
def pointBounds43520 : List (Nat × Nat × Nat) := [(5708263424,109924416261706,109924802388790)]
theorem point_links_checked43520 : (cuts43520.take 1).map (fun c => (5708185601-1+2*2^10*c.k,109924243971131+c.lower,109924630098112+c.upper)) = pointBounds43520 := by
 decide +kernel
def cuts43521 : List PrefixCut := [⟨62,280075503,280075667⟩,
⟨64,290085129,290085298⟩]
theorem checked43521 : checkPrefixCuts (2^48) 5708316673 10 Manual.Count131072.C043521.packed 64 cuts43521 = true := by
 decide +kernel
def pointBounds43521 : List (Nat × Nat × Nat) := [(5708443648,109924811081219,109925197208534)]
theorem point_links_checked43521 : (cuts43521.take 1).map (fun c => (5708316673-1+2*2^10*c.k,109924531005716+c.lower,109924917132867+c.upper)) = pointBounds43521 := by
 decide +kernel
def cuts43522 : List PrefixCut := [⟨64,287267891,287268060⟩]
theorem checked43522 : checkPrefixCuts (2^48) 5708447745 10 Manual.Count131072.C043522.packed 64 cuts43522 = true := by
 decide +kernel
def cuts43523 : List PrefixCut := [⟨22,100833130,100833183⟩,
⟨64,289036393,289036554⟩]
theorem checked43523 : checkPrefixCuts (2^48) 5708578817 10 Manual.Count131072.C043523.packed 64 cuts43523 = true := by
 decide +kernel
def pointBounds43523 : List (Nat × Nat × Nat) := [(5708623872,109925209191866,109925595319408)]
theorem point_links_checked43523 : (cuts43523.take 1).map (fun c => (5708578817-1+2*2^10*c.k,109925108358736+c.lower,109925494486225+c.upper)) = pointBounds43523 := by
 decide +kernel
def cuts43524 : List PrefixCut := [⟨46,206837870,206837990⟩,
⟨64,286958898,286959066⟩]
theorem checked43524 : checkPrefixCuts (2^48) 5708709889 10 Manual.Count131072.C043524.packed 64 cuts43524 = true := by
 decide +kernel
def pointBounds43524 : List (Nat × Nat × Nat) := [(5708804096,109925604232999,109925990360769)]
theorem point_links_checked43524 : (cuts43524.take 1).map (fun c => (5708709889-1+2*2^10*c.k,109925397395129+c.lower,109925783522779+c.upper)) = pointBounds43524 := by
 decide +kernel
def cuts43525 : List PrefixCut := [⟨64,288234213,288234386⟩]
theorem checked43525 : checkPrefixCuts (2^48) 5708840961 10 Manual.Count131072.C043525.packed 64 cuts43525 = true := by
 decide +kernel
def cuts43526 : List PrefixCut := [⟨6,27067842,27067857⟩,
⟨64,285121505,285121668⟩]
theorem checked43526 : checkPrefixCuts (2^48) 5708972033 10 Manual.Count131072.C043526.packed 64 cuts43526 = true := by
 decide +kernel
def pointBounds43526 : List (Nat × Nat × Nat) := [(5708984320,109925999656082,109926385784088)]
theorem point_links_checked43526 : (cuts43526.take 1).map (fun c => (5708972033-1+2*2^10*c.k,109925972588240+c.lower,109926358716231+c.upper)) = pointBounds43526 := by
 decide +kernel
def cuts43527 : List PrefixCut := [⟨30,135680638,135680717⟩,
⟨64,291228420,291228589⟩]
theorem checked43527 : checkPrefixCuts (2^48) 5709103105 10 Manual.Count131072.C043527.packed 64 cuts43527 = true := by
 decide +kernel
def pointBounds43527 : List (Nat × Nat × Nat) := [(5709164544,109926393390383,109926779518616)]
theorem point_links_checked43527 : (cuts43527.take 1).map (fun c => (5709103105-1+2*2^10*c.k,109926257709745+c.lower,109926643837899+c.upper)) = pointBounds43527 := by
 decide +kernel
def cuts43528 : List PrefixCut := [⟨54,244879136,244879273⟩,
⟨64,288806012,288806175⟩]
theorem checked43528 : checkPrefixCuts (2^48) 5709234177 10 Manual.Count131072.C043528.packed 64 cuts43528 = true := by
 decide +kernel
def pointBounds43528 : List (Nat × Nat × Nat) := [(5709344768,109926793817301,109927179945761)]
theorem point_links_checked43528 : (cuts43528.take 1).map (fun c => (5709234177-1+2*2^10*c.k,109926548938165+c.lower,109926935066488+c.upper)) = pointBounds43528 := by
 decide +kernel
def cuts43529 : List PrefixCut := [⟨64,283277757,283277927⟩]
theorem checked43529 : checkPrefixCuts (2^48) 5709365249 10 Manual.Count131072.C043529.packed 64 cuts43529 = true := by
 decide +kernel
def cuts43530 : List PrefixCut := [⟨14,65075079,65075116⟩,
⟨64,291208375,291208540⟩]
theorem checked43530 : checkPrefixCuts (2^48) 5709496321 10 Manual.Count131072.C043530.packed 64 cuts43530 = true := by
 decide +kernel
def pointBounds43530 : List (Nat × Nat × Nat) := [(5709524992,109927186097013,109927572225706)]
theorem point_links_checked43530 : (cuts43530.take 1).map (fun c => (5709496321-1+2*2^10*c.k,109927121021934+c.lower,109927507150590+c.upper)) = pointBounds43530 := by
 decide +kernel
def cuts43531 : List PrefixCut := [⟨38,171359723,171359822⟩,
⟨64,288786108,288786280⟩]
theorem checked43531 : checkPrefixCuts (2^48) 5709627393 10 Manual.Count131072.C043531.packed 64 cuts43531 = true := by
 decide +kernel
def pointBounds43531 : List (Nat × Nat × Nat) := [(5709705216,109927583590032,109927969718952)]
theorem point_links_checked43531 : (cuts43531.take 1).map (fun c => (5709627393-1+2*2^10*c.k,109927412230309+c.lower,109927798359130+c.upper)) = pointBounds43531 := by
 decide +kernel
def cuts43532 : List PrefixCut := [⟨62,278427299,278427462⟩,
⟨64,287547069,287547236⟩]
theorem checked43532 : checkPrefixCuts (2^48) 5709758465 10 Manual.Count131072.C043532.packed 64 cuts43532 = true := by
 decide +kernel
def pointBounds43532 : List (Nat × Nat × Nat) := [(5709885440,109927979443716,109928365572872)]
theorem point_links_checked43532 : (cuts43532.take 1).map (fun c => (5709758465-1+2*2^10*c.k,109927701016417+c.lower,109928087145410+c.upper)) = pointBounds43532 := by
 decide +kernel
def cuts43533 : List PrefixCut := [⟨64,285470017,285470183⟩]
theorem checked43533 : checkPrefixCuts (2^48) 5709889537 10 Manual.Count131072.C043533.packed 64 cuts43533 = true := by
 decide +kernel
def cuts43534 : List PrefixCut := [⟨22,99328829,99328885⟩,
⟨64,291083013,291083182⟩]
theorem checked43534 : checkPrefixCuts (2^48) 5710020609 10 Manual.Count131072.C043534.packed 64 cuts43534 = true := by
 decide +kernel
def pointBounds43534 : List (Nat × Nat × Nat) := [(5710065664,109928373362332,109928759491714)]
theorem point_links_checked43534 : (cuts43534.take 1).map (fun c => (5710020609-1+2*2^10*c.k,109928274033503+c.lower,109928660162829+c.upper)) = pointBounds43534 := by
 decide +kernel
def cuts43535 : List PrefixCut := [⟨46,204863185,204863305⟩,
⟨64,285309030,285309195⟩]
theorem checked43535 : checkPrefixCuts (2^48) 5710151681 10 Manual.Count131072.C043535.packed 64 cuts43535 = true := by
 decide +kernel
def pointBounds43535 : List (Nat × Nat × Nat) := [(5710245888,109928769979701,109929156109316)]
theorem point_links_checked43535 : (cuts43535.take 1).map (fun c => (5710151681-1+2*2^10*c.k,109928565116516+c.lower,109928951246011+c.upper)) = pointBounds43535 := by
 decide +kernel
def cuts43536 : List PrefixCut := [⟨64,286978426,286978595⟩]
theorem checked43536 : checkPrefixCuts (2^48) 5710282753 10 Manual.Count131072.C043536.packed 64 cuts43536 = true := by
 decide +kernel
def cuts43537 : List PrefixCut := [⟨6,27800379,27800395⟩,
⟨64,289781453,289781623⟩]
theorem checked43537 : checkPrefixCuts (2^48) 5710413825 10 Manual.Count131072.C043537.packed 64 cuts43537 = true := by
 decide +kernel
def pointBounds43537 : List (Nat × Nat × Nat) := [(5710426112,109929165204351,109929551334196)]
theorem point_links_checked43537 : (cuts43537.take 1).map (fun c => (5710413825-1+2*2^10*c.k,109929137403972+c.lower,109929523533801+c.upper)) = pointBounds43537 := by
 decide +kernel
def cuts43538 : List PrefixCut := [⟨30,136089987,136090062⟩,
⟨64,289281904,289282066⟩]
theorem checked43538 : checkPrefixCuts (2^48) 5710544897 10 Manual.Count131072.C043538.packed 64 cuts43538 = true := by
 decide +kernel
def pointBounds43538 : List (Nat × Nat × Nat) := [(5710606336,109929563275412,109929949405486)]
theorem point_links_checked43538 : (cuts43538.take 1).map (fun c => (5710544897-1+2*2^10*c.k,109929427185425+c.lower,109929813315424+c.upper)) = pointBounds43538 := by
 decide +kernel
def cuts43539 : List PrefixCut := [⟨54,241268510,241268653⟩,
⟨64,287500841,287501011⟩]
theorem checked43539 : checkPrefixCuts (2^48) 5710675969 10 Manual.Count131072.C043539.packed 64 cuts43539 = true := by
 decide +kernel
def pointBounds43539 : List (Nat × Nat × Nat) := [(5710786560,109929957735839,109930343866143)]
theorem point_links_checked43539 : (cuts43539.take 1).map (fun c => (5710675969-1+2*2^10*c.k,109929716467329+c.lower,109930102597490+c.upper)) = pointBounds43539 := by
 decide +kernel
def cuts43540 : List PrefixCut := [⟨64,289170017,289170186⟩]
theorem checked43540 : checkPrefixCuts (2^48) 5710807041 10 Manual.Count131072.C043540.packed 64 cuts43540 = true := by
 decide +kernel
def cuts43541 : List PrefixCut := [⟨14,60129965,60130000⟩,
⟨64,285762631,285762795⟩]
theorem checked43541 : checkPrefixCuts (2^48) 5710938113 10 Manual.Count131072.C043541.packed 64 cuts43541 = true := by
 decide +kernel
def pointBounds43541 : List (Nat × Nat × Nat) := [(5710966784,109930353268152,109930739398687)]
theorem point_links_checked43541 : (cuts43541.take 1).map (fun c => (5710938113-1+2*2^10*c.k,109930293138187+c.lower,109930679268687+c.upper)) = pointBounds43541 := by
 decide +kernel
def cuts43542 : List PrefixCut := [⟨38,172302147,172302251⟩,
⟨64,290290317,290290489⟩]
theorem checked43542 : checkPrefixCuts (2^48) 5711069185 10 Manual.Count131072.C043542.packed 64 cuts43542 = true := by
 decide +kernel
def pointBounds43542 : List (Nat × Nat × Nat) := [(5711147008,109930751202965,109931137333733)]
theorem point_links_checked43542 : (cuts43542.take 1).map (fun c => (5711069185-1+2*2^10*c.k,109930578900818+c.lower,109930965031482+c.upper)) = pointBounds43542 := by
 decide +kernel
def cuts43543 : List PrefixCut := [⟨62,276040617,276040779⟩,
⟨64,285158084,285158252⟩]
theorem checked43543 : checkPrefixCuts (2^48) 5711200257 10 Manual.Count131072.C043543.packed 64 cuts43543 = true := by
 decide +kernel
def pointBounds43543 : List (Nat × Nat × Nat) := [(5711327232,109931145231752,109931531362750)]
theorem point_links_checked43543 : (cuts43543.take 1).map (fun c => (5711200257-1+2*2^10*c.k,109930869191135+c.lower,109931255321971+c.upper)) = pointBounds43543 := by
 decide +kernel
def cuts43544 : List PrefixCut := [⟨64,284658733,284658902⟩]
theorem checked43544 : checkPrefixCuts (2^48) 5711331329 10 Manual.Count131072.C043544.packed 64 cuts43544 = true := by
 decide +kernel
def cuts43545 : List PrefixCut := [⟨22,98860219,98860272⟩,
⟨64,289136854,289137017⟩]
theorem checked43545 : checkPrefixCuts (2^48) 5711462401 10 Manual.Count131072.C043545.packed 64 cuts43545 = true := by
 decide +kernel
def pointBounds43545 : List (Nat × Nat × Nat) := [(5711507456,109931537868171,109931923999397)]
theorem point_links_checked43545 : (cuts43545.take 1).map (fun c => (5711462401-1+2*2^10*c.k,109931439007952+c.lower,109931825139125+c.upper)) = pointBounds43545 := by
 decide +kernel
def cuts43546 : List PrefixCut := [⟨46,208113318,208113446⟩,
⟨64,288489574,288489751⟩]
theorem checked43546 : checkPrefixCuts (2^48) 5711593473 10 Manual.Count131072.C043546.packed 64 cuts43546 = true := by
 decide +kernel
def pointBounds43546 : List (Nat × Nat × Nat) := [(5711687680,109931936258124,109932322389588)]
theorem point_links_checked43546 : (cuts43546.take 1).map (fun c => (5711593473-1+2*2^10*c.k,109931728144806+c.lower,109932114276142+c.upper)) = pointBounds43546 := by
 decide +kernel
def cuts43547 : List PrefixCut := [⟨64,288680071,288680239⟩]
theorem checked43547 : checkPrefixCuts (2^48) 5711724545 10 Manual.Count131072.C043547.packed 64 cuts43547 = true := by
 decide +kernel
def cuts43548 : List PrefixCut := [⟨6,27349850,27349868⟩,
⟨64,289067688,289067859⟩]
theorem checked43548 : checkPrefixCuts (2^48) 5711855617 10 Manual.Count131072.C043548.packed 64 cuts43548 = true := by
 decide +kernel
def pointBounds43548 : List (Nat × Nat × Nat) := [(5711867904,109932332664301,109932718796000)]
theorem point_links_checked43548 : (cuts43548.take 1).map (fun c => (5711855617-1+2*2^10*c.k,109932305314451+c.lower,109932691446132+c.upper)) = pointBounds43548 := by
 decide +kernel
def cuts43549 : List PrefixCut := [⟨30,135759978,135760059⟩,
⟨64,288026226,288026397⟩]
theorem checked43549 : checkPrefixCuts (2^48) 5711986689 10 Manual.Count131072.C043549.packed 64 cuts43549 = true := by
 decide +kernel
def pointBounds43549 : List (Nat × Nat × Nat) := [(5712048128,109932730142117,109933116274050)]
theorem point_links_checked43549 : (cuts43549.take 1).map (fun c => (5711986689-1+2*2^10*c.k,109932594382139+c.lower,109932980513991+c.upper)) = pointBounds43549 := by
 decide +kernel
def cuts43550 : List PrefixCut := [⟨54,240271374,240271522⟩,
⟨64,287231172,287231348⟩]
theorem checked43550 : checkPrefixCuts (2^48) 5712117761 10 Manual.Count131072.C043550.packed 64 cuts43550 = true := by
 decide +kernel
def pointBounds43550 : List (Nat × Nat × Nat) := [(5712228352,109933122679739,109933508811910)]
theorem point_links_checked43550 : (cuts43550.take 1).map (fun c => (5712117761-1+2*2^10*c.k,109932882408365+c.lower,109933268540388+c.upper)) = pointBounds43550 := by
 decide +kernel
def cuts43551 : List PrefixCut := [⟨64,283331847,283332009⟩]
theorem checked43551 : checkPrefixCuts (2^48) 5712248833 10 Manual.Count131072.C043551.packed 64 cuts43551 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000110
