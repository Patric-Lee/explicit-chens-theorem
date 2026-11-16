import PlattAssemblyKernel
import PlattCertificates.Count131072.C029632
import PlattCertificates.Count131072.C029633
import PlattCertificates.Count131072.C029634
import PlattCertificates.Count131072.C029635
import PlattCertificates.Count131072.C029636
import PlattCertificates.Count131072.C029637
import PlattCertificates.Count131072.C029638
import PlattCertificates.Count131072.C029639
import PlattCertificates.Count131072.C029640
import PlattCertificates.Count131072.C029641
import PlattCertificates.Count131072.C029642
import PlattCertificates.Count131072.C029643
import PlattCertificates.Count131072.C029644
import PlattCertificates.Count131072.C029645
import PlattCertificates.Count131072.C029646
import PlattCertificates.Count131072.C029647
import PlattCertificates.Count131072.C029648
import PlattCertificates.Count131072.C029649
import PlattCertificates.Count131072.C029650
import PlattCertificates.Count131072.C029651
import PlattCertificates.Count131072.C029652
import PlattCertificates.Count131072.C029653
import PlattCertificates.Count131072.C029654
import PlattCertificates.Count131072.C029655
import PlattCertificates.Count131072.C029656
import PlattCertificates.Count131072.C029657
import PlattCertificates.Count131072.C029658
import PlattCertificates.Count131072.C029659
import PlattCertificates.Count131072.C029660
import PlattCertificates.Count131072.C029661
import PlattCertificates.Count131072.C029662
import PlattCertificates.Count131072.C029663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000301
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29632 : List PrefixCut := [⟨12,40036282,40036306⟩,
⟨128,430763518,430763763⟩]
theorem checked29632 : checkPrefixCuts (2^48) 3887857665 9 Manual.Count131072.C029632.packed 128 cuts29632 = true := by
 decide +kernel
def pointBounds29632 : List (Nat × Nat × Nat) := [(3887869952,105070933207889,105071316440981)]
theorem point_links_checked29632 : (cuts29632.take 1).map (fun c => (3887857665-1+2*2^9*c.k,105070893171607+c.lower,105071276404675+c.upper)) = pointBounds29632 := by
 decide +kernel
def cuts29633 : List PrefixCut := [⟨3,10787002,10787008⟩,
⟨122,407293451,407293684⟩,
⟨128,429301116,429301361⟩]
theorem checked29633 : checkPrefixCuts (2^48) 3887988737 9 Manual.Count131072.C029633.packed 128 cuts29633 = true := by
 decide +kernel
def pointBounds29633 : List (Nat × Nat × Nat) := [(3887991808,105071334722127,105071717955446),(3888113664,105071731228576,105072114462122)]
theorem point_links_checked29633 : (cuts29633.take 2).map (fun c => (3887988737-1+2*2^9*c.k,105071323935125+c.lower,105071707168438+c.upper)) = pointBounds29633 := by
 decide +kernel
def cuts29634 : List PrefixCut := [⟨113,382304835,382305045⟩,
⟨128,433702643,433702880⟩]
theorem checked29634 : checkPrefixCuts (2^48) 3888119809 9 Manual.Count131072.C029634.packed 128 cuts29634 = true := by
 decide +kernel
def pointBounds29634 : List (Nat × Nat × Nat) := [(3888235520,105072135541076,105072518774844)]
theorem point_links_checked29634 : (cuts29634.take 1).map (fun c => (3888119809-1+2*2^9*c.k,105071753236241+c.lower,105072136469799+c.upper)) = pointBounds29634 := by
 decide +kernel
def cuts29635 : List PrefixCut := [⟨104,351237005,351237201⟩,
⟨128,427100595,427100834⟩]
theorem checked29635 : checkPrefixCuts (2^48) 3888250881 9 Manual.Count131072.C029635.packed 128 cuts29635 = true := by
 decide +kernel
def pointBounds29635 : List (Nat × Nat × Nat) := [(3888357376,105072538175889,105072921409880)]
theorem point_links_checked29635 : (cuts29635.take 1).map (fun c => (3888250881-1+2*2^9*c.k,105072186938884+c.lower,105072570172679+c.upper)) = pointBounds29635 := by
 decide +kernel
def cuts29636 : List PrefixCut := [⟨95,320750298,320750478⟩,
⟨128,433890498,433890740⟩]
theorem checked29636 : checkPrefixCuts (2^48) 3888381953 9 Manual.Count131072.C029636.packed 128 cuts29636 = true := by
 decide +kernel
def pointBounds29636 : List (Nat × Nat × Nat) := [(3888479232,105072934789777,105073318023991)]
theorem point_links_checked29636 : (cuts29636.take 1).map (fun c => (3888381953-1+2*2^9*c.k,105072614039479+c.lower,105072997273513+c.upper)) = pointBounds29636 := by
 decide +kernel
def cuts29637 : List PrefixCut := [⟨86,284547131,284547295⟩,
⟨128,426709733,426709974⟩]
theorem checked29637 : checkPrefixCuts (2^48) 3888513025 9 Manual.Count131072.C029637.packed 128 cuts29637 = true := by
 decide +kernel
def pointBounds29637 : List (Nat × Nat × Nat) := [(3888601088,105073332477108,105073715711548)]
theorem point_links_checked29637 : (cuts29637.take 1).map (fun c => (3888513025-1+2*2^9*c.k,105073047929977+c.lower,105073431164253+c.upper)) = pointBounds29637 := by
 decide +kernel
def cuts29638 : List PrefixCut := [⟨77,259855277,259855421⟩,
⟨128,433209838,433210077⟩]
theorem checked29638 : checkPrefixCuts (2^48) 3888644097 9 Manual.Count131072.C029638.packed 128 cuts29638 = true := by
 decide +kernel
def pointBounds29638 : List (Nat × Nat × Nat) := [(3888722944,105073734494987,105074117729648)]
theorem point_links_checked29638 : (cuts29638.take 1).map (fun c => (3888644097-1+2*2^9*c.k,105073474639710+c.lower,105073857874227+c.upper)) = pointBounds29638 := by
 decide +kernel
def cuts29639 : List PrefixCut := [⟨68,224452633,224452760⟩,
⟨128,425667651,425667891⟩]
theorem checked29639 : checkPrefixCuts (2^48) 3888775169 9 Manual.Count131072.C029639.packed 128 cuts29639 = true := by
 decide +kernel
def pointBounds29639 : List (Nat × Nat × Nat) := [(3888844800,105074132302181,105074515537064)]
theorem point_links_checked29639 : (cuts29639.take 1).map (fun c => (3888775169-1+2*2^9*c.k,105073907849548+c.lower,105074291084304+c.upper)) = pointBounds29639 := by
 decide +kernel
def cuts29640 : List PrefixCut := [⟨59,196290183,196290297⟩,
⟨128,430575044,430575289⟩]
theorem checked29640 : checkPrefixCuts (2^48) 3888906241 9 Manual.Count131072.C029640.packed 128 cuts29640 = true := by
 decide +kernel
def pointBounds29640 : List (Nat × Nat × Nat) := [(3888966656,105074529807382,105074913042492)]
theorem point_links_checked29640 : (cuts29640.take 1).map (fun c => (3888906241-1+2*2^9*c.k,105074333517199+c.lower,105074716752195+c.upper)) = pointBounds29640 := by
 decide +kernel
def cuts29641 : List PrefixCut := [⟨50,166681992,166682083⟩,
⟨128,427086537,427086772⟩]
theorem checked29641 : checkPrefixCuts (2^48) 3889037313 9 Manual.Count131072.C029641.packed 128 cuts29641 = true := by
 decide +kernel
def pointBounds29641 : List (Nat × Nat × Nat) := [(3889088512,105074930774235,105075314009567)]
theorem point_links_checked29641 : (cuts29641.take 1).map (fun c => (3889037313-1+2*2^9*c.k,105074764092243+c.lower,105075147327484+c.upper)) = pointBounds29641 := by
 decide +kernel
def cuts29642 : List PrefixCut := [⟨41,139536434,139536508⟩,
⟨128,428447246,428447480⟩]
theorem checked29642 : checkPrefixCuts (2^48) 3889168385 9 Manual.Count131072.C029642.packed 128 cuts29642 = true := by
 decide +kernel
def pointBounds29642 : List (Nat × Nat × Nat) := [(3889210368,105075330715214,105075713950764)]
theorem point_links_checked29642 : (cuts29642.take 1).map (fun c => (3889168385-1+2*2^9*c.k,105075191178780+c.lower,105075574414256+c.upper)) = pointBounds29642 := by
 decide +kernel
def cuts29643 : List PrefixCut := [⟨32,107254285,107254347⟩,
⟨128,427998532,427998773⟩]
theorem checked29643 : checkPrefixCuts (2^48) 3889299457 9 Manual.Count131072.C029643.packed 128 cuts29643 = true := by
 decide +kernel
def pointBounds29643 : List (Nat × Nat × Nat) := [(3889332224,105075726880311,105076110116083)]
theorem point_links_checked29643 : (cuts29643.take 1).map (fun c => (3889299457-1+2*2^9*c.k,105075619626026+c.lower,105076002861736+c.upper)) = pointBounds29643 := by
 decide +kernel
def cuts29644 : List PrefixCut := [⟨23,73165016,73165058⟩,
⟨128,427115667,427115904⟩]
theorem checked29644 : checkPrefixCuts (2^48) 3889430529 9 Manual.Count131072.C029644.packed 128 cuts29644 = true := by
 decide +kernel
def pointBounds29644 : List (Nat × Nat × Nat) := [(3889454080,105076120789574,105076504025567)]
theorem point_links_checked29644 : (cuts29644.take 1).map (fun c => (3889430529-1+2*2^9*c.k,105076047624558+c.lower,105076430860509+c.upper)) = pointBounds29644 := by
 decide +kernel
def cuts29645 : List PrefixCut := [⟨14,48196160,48196187⟩,
⟨128,429706461,429706702⟩]
theorem checked29645 : checkPrefixCuts (2^48) 3889561601 9 Manual.Count131072.C029645.packed 128 cuts29645 = true := by
 decide +kernel
def pointBounds29645 : List (Nat × Nat × Nat) := [(3889575936,105076522936385,105076906172600)]
theorem point_links_checked29645 : (cuts29645.take 1).map (fun c => (3889561601-1+2*2^9*c.k,105076474740225+c.lower,105076857976413+c.upper)) = pointBounds29645 := by
 decide +kernel
def cuts29646 : List PrefixCut := [⟨5,16426686,16426695⟩,
⟨124,418258829,418259063⟩,
⟨128,431211610,431211851⟩]
theorem checked29646 : checkPrefixCuts (2^48) 3889692673 9 Manual.Count131072.C029646.packed 128 cuts29646 = true := by
 decide +kernel
def pointBounds29646 : List (Nat × Nat × Nat) := [(3889697792,105076920873372,105077304109810),(3889819648,105077322705515,105077705942178)]
theorem point_links_checked29646 : (cuts29646.take 2).map (fun c => (3889692673-1+2*2^9*c.k,105076904446686+c.lower,105077287683115+c.upper)) = pointBounds29646 := by
 decide +kernel
def cuts29647 : List PrefixCut := [⟨115,384235641,384235857⟩,
⟨128,427506653,427506893⟩]
theorem checked29647 : checkPrefixCuts (2^48) 3889823745 9 Manual.Count131072.C029647.packed 128 cuts29647 = true := by
 decide +kernel
def pointBounds29647 : List (Nat × Nat × Nat) := [(3889941504,105077719893937,105078103130823)]
theorem point_links_checked29647 : (cuts29647.take 1).map (fun c => (3889823745-1+2*2^9*c.k,105077335658296+c.lower,105077718894966+c.upper)) = pointBounds29647 := by
 decide +kernel
def cuts29648 : List PrefixCut := [⟨106,357595337,357595537⟩,
⟨128,432123254,432123497⟩]
theorem checked29648 : checkPrefixCuts (2^48) 3889954817 9 Manual.Count131072.C029648.packed 128 cuts29648 = true := by
 decide +kernel
def pointBounds29648 : List (Nat × Nat × Nat) := [(3890063360,105078120760286,105078503997396)]
theorem point_links_checked29648 : (cuts29648.take 1).map (fun c => (3889954817-1+2*2^9*c.k,105077763164949+c.lower,105078146401859+c.upper)) = pointBounds29648 := by
 decide +kernel
def cuts29649 : List PrefixCut := [⟨97,326759979,326760160⟩,
⟨128,434062224,434062467⟩]
theorem checked29649 : checkPrefixCuts (2^48) 3890085889 9 Manual.Count131072.C029649.packed 128 cuts29649 = true := by
 decide +kernel
def pointBounds29649 : List (Nat × Nat × Nat) := [(3890185216,105078522048182,105078905285516)]
theorem point_links_checked29649 : (cuts29649.take 1).map (fun c => (3890085889-1+2*2^9*c.k,105078195288203+c.lower,105078578525356+c.upper)) = pointBounds29649 := by
 decide +kernel
def cuts29650 : List PrefixCut := [⟨88,291874841,291875005⟩,
⟨128,423628735,423628979⟩]
theorem checked29650 : checkPrefixCuts (2^48) 3890216961 9 Manual.Count131072.C029650.packed 128 cuts29650 = true := by
 decide +kernel
def pointBounds29650 : List (Nat × Nat × Nat) := [(3890307072,105078921225268,105079304462828)]
theorem point_links_checked29650 : (cuts29650.take 1).map (fun c => (3890216961-1+2*2^9*c.k,105078629350427+c.lower,105079012587823+c.upper)) = pointBounds29650 := by
 decide +kernel
def cuts29651 : List PrefixCut := [⟨79,265167723,265167870⟩,
⟨128,426002079,426002318⟩]
theorem checked29651 : checkPrefixCuts (2^48) 3890348033 9 Manual.Count131072.C029651.packed 128 cuts29651 = true := by
 decide +kernel
def pointBounds29651 : List (Nat × Nat × Nat) := [(3890428928,105079318146885,105079701384672)]
theorem point_links_checked29651 : (cuts29651.take 1).map (fun c => (3890348033-1+2*2^9*c.k,105079052979162+c.lower,105079436216802+c.upper)) = pointBounds29651 := by
 decide +kernel
def cuts29652 : List PrefixCut := [⟨70,236147163,236147293⟩,
⟨128,426277156,426277397⟩]
theorem checked29652 : checkPrefixCuts (2^48) 3890479105 9 Manual.Count131072.C029652.packed 128 cuts29652 = true := by
 decide +kernel
def pointBounds29652 : List (Nat × Nat × Nat) := [(3890550784,105079715128404,105080098366413)]
theorem point_links_checked29652 : (cuts29652.take 1).map (fun c => (3890479105-1+2*2^9*c.k,105079478981241+c.lower,105079862219120+c.upper)) = pointBounds29652 := by
 decide +kernel
def cuts29653 : List PrefixCut := [⟨61,205753897,205754011⟩,
⟨128,435378289,435378534⟩]
theorem checked29653 : checkPrefixCuts (2^48) 3890610177 9 Manual.Count131072.C029653.packed 128 cuts29653 = true := by
 decide +kernel
def pointBounds29653 : List (Nat × Nat × Nat) := [(3890672640,105080111012294,105080494250528)]
theorem point_links_checked29653 : (cuts29653.take 1).map (fun c => (3890610177-1+2*2^9*c.k,105079905258397+c.lower,105080288496517+c.upper)) = pointBounds29653 := by
 decide +kernel
def cuts29654 : List PrefixCut := [⟨52,175073220,175073319⟩,
⟨128,433265719,433265964⟩]
theorem checked29654 : checkPrefixCuts (2^48) 3890741249 9 Manual.Count131072.C029654.packed 128 cuts29654 = true := by
 decide +kernel
def pointBounds29654 : List (Nat × Nat × Nat) := [(3890794496,105080515709906,105080898948370)]
theorem point_links_checked29654 : (cuts29654.take 1).map (fun c => (3890741249-1+2*2^9*c.k,105080340636686+c.lower,105080723875051+c.upper)) = pointBounds29654 := by
 decide +kernel
def cuts29655 : List PrefixCut := [⟨43,145262647,145262728⟩,
⟨128,428404298,428404540⟩]
theorem checked29655 : checkPrefixCuts (2^48) 3890872321 9 Manual.Count131072.C029655.packed 128 cuts29655 = true := by
 decide +kernel
def pointBounds29655 : List (Nat × Nat × Nat) := [(3890916352,105080919165052,105081302403743)]
theorem point_links_checked29655 : (cuts29655.take 1).map (fun c => (3890872321-1+2*2^9*c.k,105080773902405+c.lower,105081157141015+c.upper)) = pointBounds29655 := by
 decide +kernel
def cuts29656 : List PrefixCut := [⟨34,111837026,111837090⟩,
⟨128,425134588,425134830⟩]
theorem checked29656 : checkPrefixCuts (2^48) 3891003393 9 Manual.Count131072.C029656.packed 128 cuts29656 = true := by
 decide +kernel
def pointBounds29656 : List (Nat × Nat × Nat) := [(3891038208,105081314143729,105081697382645)]
theorem point_links_checked29656 : (cuts29656.take 1).map (fun c => (3891003393-1+2*2^9*c.k,105081202306703+c.lower,105081585545555+c.upper)) = pointBounds29656 := by
 decide +kernel
def cuts29657 : List PrefixCut := [⟨25,84128221,84128266⟩,
⟨128,431413479,431413718⟩]
theorem checked29657 : checkPrefixCuts (2^48) 3891134465 9 Manual.Count131072.C029657.packed 128 cuts29657 = true := by
 decide +kernel
def pointBounds29657 : List (Nat × Nat × Nat) := [(3891160064,105081711569512,105082094808651)]
theorem point_links_checked29657 : (cuts29657.take 1).map (fun c => (3891134465-1+2*2^9*c.k,105081627441291+c.lower,105082010680385+c.upper)) = pointBounds29657 := by
 decide +kernel
def cuts29658 : List PrefixCut := [⟨16,54323509,54323539⟩,
⟨128,427492969,427493210⟩]
theorem checked29658 : checkPrefixCuts (2^48) 3891265537 9 Manual.Count131072.C029658.packed 128 cuts29658 = true := by
 decide +kernel
def pointBounds29658 : List (Nat × Nat × Nat) := [(3891281920,105082113178279,105082496417642)]
theorem point_links_checked29658 : (cuts29658.take 1).map (fun c => (3891265537-1+2*2^9*c.k,105082058854770+c.lower,105082442094103+c.upper)) = pointBounds29658 := by
 decide +kernel
def cuts29659 : List PrefixCut := [⟨7,23435745,23435758⟩,
⟨126,422560093,422560328⟩,
⟨128,428997481,428997719⟩]
theorem checked29659 : checkPrefixCuts (2^48) 3891396609 9 Manual.Count131072.C029659.packed 128 cuts29659 = true := by
 decide +kernel
def pointBounds29659 : List (Nat × Nat × Nat) := [(3891403776,105082509783484,105082893023071),(3891525632,105082908907832,105083292147641)]
theorem point_links_checked29659 : (cuts29659.take 2).map (fun c => (3891396609-1+2*2^9*c.k,105082486347739+c.lower,105082869587313+c.upper)) = pointBounds29659 := by
 decide +kernel
def cuts29660 : List PrefixCut := [⟨117,393036165,393036388⟩,
⟨128,428983105,428983349⟩]
theorem checked29660 : checkPrefixCuts (2^48) 3891527681 9 Manual.Count131072.C029660.packed 128 cuts29660 = true := by
 decide +kernel
def pointBounds29660 : List (Nat × Nat × Nat) := [(3891647488,105083308381385,105083691621420)]
theorem point_links_checked29660 : (cuts29660.take 1).map (fun c => (3891527681-1+2*2^9*c.k,105082915345220+c.lower,105083298585032+c.upper)) = pointBounds29660 := by
 decide +kernel
def cuts29661 : List PrefixCut := [⟨108,355413463,355413663⟩,
⟨128,423905709,423905949⟩]
theorem checked29661 : checkPrefixCuts (2^48) 3891658753 9 Manual.Count131072.C029661.packed 128 cuts29661 = true := by
 decide +kernel
def pointBounds29661 : List (Nat × Nat × Nat) := [(3891769344,105083699741788,105084082982044)]
theorem point_links_checked29661 : (cuts29661.take 1).map (fun c => (3891658753-1+2*2^9*c.k,105083344328325+c.lower,105083727568381+c.upper)) = pointBounds29661 := by
 decide +kernel
def cuts29662 : List PrefixCut := [⟨99,331968826,331969013⟩,
⟨128,429098811,429099052⟩]
theorem checked29662 : checkPrefixCuts (2^48) 3891789825 9 Manual.Count131072.C029662.packed 128 cuts29662 = true := by
 decide +kernel
def pointBounds29662 : List (Nat × Nat × Nat) := [(3891891200,105084100202860,105084483443343)]
theorem point_links_checked29662 : (cuts29662.take 1).map (fun c => (3891789825-1+2*2^9*c.k,105083768234034+c.lower,105084151474330+c.upper)) = pointBounds29662 := by
 decide +kernel
def cuts29663 : List PrefixCut := [⟨90,301655137,301655304⟩,
⟨128,424672818,424673054⟩]
theorem checked29663 : checkPrefixCuts (2^48) 3891920897 9 Manual.Count131072.C029663.packed 128 cuts29663 = true := by
 decide +kernel
def pointBounds29663 : List (Nat × Nat × Nat) := [(3892013056,105084498987982,105084882228686)]
theorem point_links_checked29663 : (cuts29663.take 1).map (fun c => (3891920897-1+2*2^9*c.k,105084197332845+c.lower,105084580573382+c.upper)) = pointBounds29663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000301
