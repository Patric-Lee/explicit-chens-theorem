import PlattAssemblyKernel
import PlattCertificates.Count131072.C030608
import PlattCertificates.Count131072.C030609
import PlattCertificates.Count131072.C030610
import PlattCertificates.Count131072.C030611
import PlattCertificates.Count131072.C030612
import PlattCertificates.Count131072.C030613
import PlattCertificates.Count131072.C030614
import PlattCertificates.Count131072.C030615
import PlattCertificates.Count131072.C030616
import PlattCertificates.Count131072.C030617
import PlattCertificates.Count131072.C030618
import PlattCertificates.Count131072.C030619
import PlattCertificates.Count131072.C030620
import PlattCertificates.Count131072.C030621
import PlattCertificates.Count131072.C030622
import PlattCertificates.Count131072.C030623
import PlattCertificates.Count131072.C030624
import PlattCertificates.Count131072.C030625
import PlattCertificates.Count131072.C030626
import PlattCertificates.Count131072.C030627
import PlattCertificates.Count131072.C030628
import PlattCertificates.Count131072.C030629
import PlattCertificates.Count131072.C030630
import PlattCertificates.Count131072.C030631
import PlattCertificates.Count131072.C030632
import PlattCertificates.Count131072.C030633
import PlattCertificates.Count131072.C030634
import PlattCertificates.Count131072.C030635
import PlattCertificates.Count131072.C030636
import PlattCertificates.Count131072.C030637
import PlattCertificates.Count131072.C030638
import PlattCertificates.Count131072.C030639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30608 : List PrefixCut := [⟨48,151608384,151608469⟩,
⟨128,411013588,411013814⟩]
theorem checked30608 : checkPrefixCuts (2^48) 4015783937 9 Manual.Count131072.C030608.packed 128 cuts30608 = true := by
 decide +kernel
def pointBounds30608 : List (Nat × Nat × Nat) := [(4015833088,105483346941317,105483730406155)]
theorem point_links_checked30608 : (cuts30608.take 1).map (fun c => (4015783937-1+2*2^9*c.k,105483195332933+c.lower,105483578797686+c.upper)) = pointBounds30608 := by
 decide +kernel
def cuts30609 : List PrefixCut := [⟨43,139548140,139548217⟩,
⟨128,414364451,414364685⟩]
theorem checked30609 : checkPrefixCuts (2^48) 4015915009 9 Manual.Count131072.C030609.packed 128 cuts30609 = true := by
 decide +kernel
def pointBounds30609 : List (Nat × Nat × Nat) := [(4015959040,105483745894661,105484129359717)]
theorem point_links_checked30609 : (cuts30609.take 1).map (fun c => (4015915009-1+2*2^9*c.k,105483606346521+c.lower,105483989811500+c.upper)) = pointBounds30609 := by
 decide +kernel
def cuts30610 : List PrefixCut := [⟨38,123353515,123353580⟩,
⟨128,419327038,419327267⟩]
theorem checked30610 : checkPrefixCuts (2^48) 4016046081 9 Manual.Count131072.C030610.packed 128 cuts30610 = true := by
 decide +kernel
def pointBounds30610 : List (Nat × Nat × Nat) := [(4016084992,105484144064487,105484527529765)]
theorem point_links_checked30610 : (cuts30610.take 1).map (fun c => (4016046081-1+2*2^9*c.k,105484020710972+c.lower,105484404176185+c.upper)) = pointBounds30610 := by
 decide +kernel
def cuts30611 : List PrefixCut := [⟨33,107580466,107580526⟩,
⟨128,424079053,424079291⟩]
theorem checked30611 : checkPrefixCuts (2^48) 4016177153 9 Manual.Count131072.C030611.packed 128 cuts30611 = true := by
 decide +kernel
def pointBounds30611 : List (Nat × Nat × Nat) := [(4016210944,105484547618476,105484931083978)]
theorem point_links_checked30611 : (cuts30611.take 1).map (fun c => (4016177153-1+2*2^9*c.k,105484440038010+c.lower,105484823503452+c.upper)) = pointBounds30611 := by
 decide +kernel
def cuts30612 : List PrefixCut := [⟨28,90757154,90757206⟩,
⟨128,411030035,411030268⟩]
theorem checked30612 : checkPrefixCuts (2^48) 4016308225 9 Manual.Count131072.C030612.packed 128 cuts30612 = true := by
 decide +kernel
def pointBounds30612 : List (Nat × Nat × Nat) := [(4016336896,105484954874217,105485338339949)]
theorem point_links_checked30612 : (cuts30612.take 1).map (fun c => (4016308225-1+2*2^9*c.k,105484864117063+c.lower,105485247582743+c.upper)) = pointBounds30612 := by
 decide +kernel
def cuts30613 : List PrefixCut := [⟨23,74916050,74916092⟩,
⟨128,415431676,415431908⟩]
theorem checked30613 : checkPrefixCuts (2^48) 4016439297 9 Manual.Count131072.C030613.packed 128 cuts30613 = true := by
 decide +kernel
def pointBounds30613 : List (Nat × Nat × Nat) := [(4016462848,105485350063148,105485733529103)]
theorem point_links_checked30613 : (cuts30613.take 1).map (fun c => (4016439297-1+2*2^9*c.k,105485275147098+c.lower,105485658613011+c.upper)) = pointBounds30613 := by
 decide +kernel
def cuts30614 : List PrefixCut := [⟨18,58024796,58024828⟩,
⟨128,418851857,418852085⟩]
theorem checked30614 : checkPrefixCuts (2^48) 4016570369 9 Manual.Count131072.C030614.packed 128 cuts30614 = true := by
 decide +kernel
def pointBounds30614 : List (Nat × Nat × Nat) := [(4016588800,105485748603570,105486132069747)]
theorem point_links_checked30614 : (cuts30614.take 1).map (fun c => (4016570369-1+2*2^9*c.k,105485690578774+c.lower,105486074044919+c.upper)) = pointBounds30614 := by
 decide +kernel
def cuts30615 : List PrefixCut := [⟨13,42956598,42956620⟩,
⟨128,414283294,414283527⟩]
theorem checked30615 : checkPrefixCuts (2^48) 4016701441 9 Manual.Count131072.C030615.packed 128 cuts30615 = true := by
 decide +kernel
def pointBounds30615 : List (Nat × Nat × Nat) := [(4016714752,105486152387229,105486535853624)]
theorem point_links_checked30615 : (cuts30615.take 1).map (fun c => (4016701441-1+2*2^9*c.k,105486109430631+c.lower,105486492897004+c.upper)) = pointBounds30615 := by
 decide +kernel
def cuts30616 : List PrefixCut := [⟨8,25927299,25927311⟩,
⟨128,415391006,415391238⟩]
theorem checked30616 : checkPrefixCuts (2^48) 4016832513 9 Manual.Count131072.C030616.packed 128 cuts30616 = true := by
 decide +kernel
def pointBounds30616 : List (Nat × Nat × Nat) := [(4016840704,105486549641224,105486933107842)]
theorem point_links_checked30616 : (cuts30616.take 1).map (fun c => (4016832513-1+2*2^9*c.k,105486523713925+c.lower,105486907180531+c.upper)) = pointBounds30616 := by
 decide +kernel
def cuts30617 : List PrefixCut := [⟨3,10020229,10020235⟩,
⟨126,406338409,406338638⟩,
⟨128,413485477,413485710⟩]
theorem checked30617 : checkPrefixCuts (2^48) 4016963585 9 Manual.Count131072.C030617.packed 128 cuts30617 = true := by
 decide +kernel
def pointBounds30617 : List (Nat × Nat × Nat) := [(4016966656,105486949125160,105487332592004),(4017092608,105487345443340,105487728910407)]
theorem point_links_checked30617 : (cuts30617.take 2).map (fun c => (4016963585-1+2*2^9*c.k,105486939104931+c.lower,105487322571769+c.upper)) = pointBounds30617 := by
 decide +kernel
def cuts30618 : List PrefixCut := [⟨121,394624043,394624265⟩,
⟨128,418026438,418026671⟩]
theorem checked30618 : checkPrefixCuts (2^48) 4017094657 9 Manual.Count131072.C030618.packed 128 cuts30618 = true := by
 decide +kernel
def pointBounds30618 : List (Nat × Nat × Nat) := [(4017218560,105487747214451,105488130681744)]
theorem point_links_checked30618 : (cuts30618.take 1).map (fun c => (4017094657-1+2*2^9*c.k,105487352590408+c.lower,105487736057479+c.upper)) = pointBounds30618 := by
 decide +kernel
def cuts30619 : List PrefixCut := [⟨116,372680706,372680922⟩,
⟨128,414018942,414019180⟩]
theorem checked30619 : checkPrefixCuts (2^48) 4017225729 9 Manual.Count131072.C030619.packed 128 cuts30619 = true := by
 decide +kernel
def pointBounds30619 : List (Nat × Nat × Nat) := [(4017344512,105488143297552,105488526765072)]
theorem point_links_checked30619 : (cuts30619.take 1).map (fun c => (4017225729-1+2*2^9*c.k,105487770616846+c.lower,105488154084150+c.upper)) = pointBounds30619 := by
 decide +kernel
def cuts30620 : List PrefixCut := [⟨111,358095579,358095775⟩,
⟨128,411903631,411903856⟩]
theorem checked30620 : checkPrefixCuts (2^48) 4017356801 9 Manual.Count131072.C030620.packed 128 cuts30620 = true := by
 decide +kernel
def pointBounds30620 : List (Nat × Nat × Nat) := [(4017470464,105488542731367,105488926199105)]
theorem point_links_checked30620 : (cuts30620.take 1).map (fun c => (4017356801-1+2*2^9*c.k,105488184635788+c.lower,105488568103330+c.upper)) = pointBounds30620 := by
 decide +kernel
def cuts30621 : List PrefixCut := [⟨106,345613224,345613420⟩,
⟨128,414832827,414833060⟩]
theorem checked30621 : checkPrefixCuts (2^48) 4017487873 9 Manual.Count131072.C030621.packed 128 cuts30621 = true := by
 decide +kernel
def pointBounds30621 : List (Nat × Nat × Nat) := [(4017596416,105488942152643,105489325620606)]
theorem point_links_checked30621 : (cuts30621.take 1).map (fun c => (4017487873-1+2*2^9*c.k,105488596539419+c.lower,105488980007186+c.upper)) = pointBounds30621 := by
 decide +kernel
def cuts30622 : List PrefixCut := [⟨101,324444285,324444470⟩,
⟨128,411736656,411736887⟩]
theorem checked30622 : checkPrefixCuts (2^48) 4017618945 9 Manual.Count131072.C030622.packed 128 cuts30622 = true := by
 decide +kernel
def pointBounds30622 : List (Nat × Nat × Nat) := [(4017722368,105489335816531,105489719284716)]
theorem point_links_checked30622 : (cuts30622.take 1).map (fun c => (4017618945-1+2*2^9*c.k,105489011372246+c.lower,105489394840246+c.upper)) = pointBounds30622 := by
 decide +kernel
def cuts30623 : List PrefixCut := [⟨96,309091405,309091579⟩,
⟨128,411092718,411092951⟩]
theorem checked30623 : checkPrefixCuts (2^48) 4017750017 9 Manual.Count131072.C030623.packed 128 cuts30623 = true := by
 decide +kernel
def pointBounds30623 : List (Nat × Nat × Nat) := [(4017848320,105489732200307,105490115668712)]
theorem point_links_checked30623 : (cuts30623.take 1).map (fun c => (4017750017-1+2*2^9*c.k,105489423108902+c.lower,105489806577133+c.upper)) = pointBounds30623 := by
 decide +kernel
def cuts30624 : List PrefixCut := [⟨91,294370056,294370225⟩,
⟨128,411849944,411850183⟩]
theorem checked30624 : checkPrefixCuts (2^48) 4017881089 9 Manual.Count131072.C030624.packed 128 cuts30624 = true := by
 decide +kernel
def pointBounds30624 : List (Nat × Nat × Nat) := [(4017974272,105490128571676,105490512040309)]
theorem point_links_checked30624 : (cuts30624.take 1).map (fun c => (4017881089-1+2*2^9*c.k,105489834201620+c.lower,105490217670084+c.upper)) = pointBounds30624 := by
 decide +kernel
def cuts30625 : List PrefixCut := [⟨86,275446444,275446598⟩,
⟨128,413447628,413447859⟩]
theorem checked30625 : checkPrefixCuts (2^48) 4018012161 9 Manual.Count131072.C030625.packed 128 cuts30625 = true := by
 decide +kernel
def pointBounds30625 : List (Nat × Nat × Nat) := [(4018100224,105490521498008,105490904966865)]
theorem point_links_checked30625 : (cuts30625.take 1).map (fun c => (4018012161-1+2*2^9*c.k,105490246051564+c.lower,105490629520267+c.upper)) = pointBounds30625 := by
 decide +kernel
def cuts30626 : List PrefixCut := [⟨81,264790026,264790176⟩,
⟨128,415815945,415816178⟩]
theorem checked30626 : checkPrefixCuts (2^48) 4018143233 9 Manual.Count131072.C030626.packed 128 cuts30626 = true := by
 decide +kernel
def pointBounds30626 : List (Nat × Nat × Nat) := [(4018226176,105490924289218,105491307758302)]
theorem point_links_checked30626 : (cuts30626.take 1).map (fun c => (4018143233-1+2*2^9*c.k,105490659499192+c.lower,105491042968126+c.upper)) = pointBounds30626 := by
 decide +kernel
def cuts30627 : List PrefixCut := [⟨76,247689806,247689947⟩,
⟨128,418394055,418394290⟩]
theorem checked30627 : checkPrefixCuts (2^48) 4018274305 9 Manual.Count131072.C030627.packed 128 cuts30627 = true := by
 decide +kernel
def pointBounds30627 : List (Nat × Nat × Nat) := [(4018352128,105491323004943,105491706474251)]
theorem point_links_checked30627 : (cuts30627.take 1).map (fun c => (4018274305-1+2*2^9*c.k,105491075315137+c.lower,105491458784304+c.upper)) = pointBounds30627 := by
 decide +kernel
def cuts30628 : List PrefixCut := [⟨71,224706870,224707000⟩,
⟨128,409484620,409484852⟩]
theorem checked30628 : checkPrefixCuts (2^48) 4018405377 9 Manual.Count131072.C030628.packed 128 cuts30628 = true := by
 decide +kernel
def pointBounds30628 : List (Nat × Nat × Nat) := [(4018478080,105491718416062,105492101885594)]
theorem point_links_checked30628 : (cuts30628.take 1).map (fun c => (4018405377-1+2*2^9*c.k,105491493709192+c.lower,105491877178594+c.upper)) = pointBounds30628 := by
 decide +kernel
def cuts30629 : List PrefixCut := [⟨66,215664089,215664211⟩,
⟨128,415635148,415635386⟩]
theorem checked30629 : checkPrefixCuts (2^48) 4018536449 9 Manual.Count131072.C030629.packed 128 cuts30629 = true := by
 decide +kernel
def pointBounds30629 : List (Nat × Nat × Nat) := [(4018604032,105492118857901,105492502327657)]
theorem point_links_checked30629 : (cuts30629.take 1).map (fun c => (4018536449-1+2*2^9*c.k,105491903193812+c.lower,105492286663446+c.upper)) = pointBounds30629 := by
 decide +kernel
def cuts30630 : List PrefixCut := [⟨61,202349329,202349439⟩,
⟨128,416392062,416392295⟩]
theorem checked30630 : checkPrefixCuts (2^48) 4018667521 9 Manual.Count131072.C030630.packed 128 cuts30630 = true := by
 decide +kernel
def pointBounds30630 : List (Nat × Nat × Nat) := [(4018729984,105492521178289,105492904648271)]
theorem point_links_checked30630 : (cuts30630.take 1).map (fun c => (4018667521-1+2*2^9*c.k,105492318828960+c.lower,105492702298832+c.upper)) = pointBounds30630 := by
 decide +kernel
def cuts30631 : List PrefixCut := [⟨56,182311691,182311792⟩,
⟨128,413436838,413437069⟩]
theorem checked30631 : checkPrefixCuts (2^48) 4018798593 9 Manual.Count131072.C030631.packed 128 cuts30631 = true := by
 decide +kernel
def pointBounds30631 : List (Nat × Nat × Nat) := [(4018855936,105492917532713,105493301002919)]
theorem point_links_checked30631 : (cuts30631.take 1).map (fun c => (4018798593-1+2*2^9*c.k,105492735221022+c.lower,105493118691127+c.upper)) = pointBounds30631 := by
 decide +kernel
def cuts30632 : List PrefixCut := [⟨51,162765573,162765666⟩,
⟨128,410481790,410482020⟩]
theorem checked30632 : checkPrefixCuts (2^48) 4018929665 9 Manual.Count131072.C030632.packed 128 cuts30632 = true := by
 decide +kernel
def pointBounds30632 : List (Nat × Nat × Nat) := [(4018981888,105493311423433,105493694893862)]
theorem point_links_checked30632 : (cuts30632.take 1).map (fun c => (4018929665-1+2*2^9*c.k,105493148657860+c.lower,105493532128196+c.upper)) = pointBounds30632 := by
 decide +kernel
def cuts30633 : List PrefixCut := [⟨46,148893527,148893605⟩,
⟨128,415650918,415651139⟩]
theorem checked30633 : checkPrefixCuts (2^48) 4019060737 9 Manual.Count131072.C030633.packed 128 cuts30633 = true := by
 decide +kernel
def pointBounds30633 : List (Nat × Nat × Nat) := [(4019107840,105493708033177,105494091503821)]
theorem point_links_checked30633 : (cuts30633.take 1).map (fun c => (4019060737-1+2*2^9*c.k,105493559139650+c.lower,105493942610216+c.upper)) = pointBounds30633 := by
 decide +kernel
def cuts30634 : List PrefixCut := [⟨41,135022356,135022430⟩,
⟨128,418648747,418648981⟩]
theorem checked30634 : checkPrefixCuts (2^48) 4019191809 9 Manual.Count131072.C030634.packed 128 cuts30634 = true := by
 decide +kernel
def pointBounds30634 : List (Nat × Nat × Nat) := [(4019233792,105494109812924,105494493283785)]
theorem point_links_checked30634 : (cuts30634.take 1).map (fun c => (4019191809-1+2*2^9*c.k,105493974790568+c.lower,105494358261355+c.upper)) = pointBounds30634 := by
 decide +kernel
def cuts30635 : List PrefixCut := [⟨36,117860674,117860740⟩,
⟨128,418845154,418845390⟩]
theorem checked30635 : checkPrefixCuts (2^48) 4019322881 9 Manual.Count131072.C030635.packed 128 cuts30635 = true := by
 decide +kernel
def pointBounds30635 : List (Nat × Nat × Nat) := [(4019359744,105494511299989,105494894771076)]
theorem point_links_checked30635 : (cuts30635.take 1).map (fun c => (4019322881-1+2*2^9*c.k,105494393439315+c.lower,105494776910336+c.upper)) = pointBounds30635 := by
 decide +kernel
def cuts30636 : List PrefixCut := [⟨31,98529210,98529269⟩,
⟨128,415050012,415050249⟩]
theorem checked30636 : checkPrefixCuts (2^48) 4019453953 9 Manual.Count131072.C030636.packed 128 cuts30636 = true := by
 decide +kernel
def pointBounds30636 : List (Nat × Nat × Nat) := [(4019485696,105494910813679,105495294284995)]
theorem point_links_checked30636 : (cuts30636.take 1).map (fun c => (4019453953-1+2*2^9*c.k,105494812284469+c.lower,105495195755726+c.upper)) = pointBounds30636 := by
 decide +kernel
def cuts30637 : List PrefixCut := [⟨26,86131521,86131566⟩,
⟨128,412655715,412655950⟩]
theorem checked30637 : checkPrefixCuts (2^48) 4019585025 9 Manual.Count131072.C030637.packed 128 cuts30637 = true := by
 decide +kernel
def pointBounds30637 : List (Nat × Nat × Nat) := [(4019611648,105495313466002,105495696937541)]
theorem point_links_checked30637 : (cuts30637.take 1).map (fun c => (4019585025-1+2*2^9*c.k,105495227334481+c.lower,105495610805975+c.upper)) = pointBounds30637 := by
 decide +kernel
def cuts30638 : List PrefixCut := [⟨21,70583576,70583614⟩,
⟨128,418384069,418384301⟩]
theorem checked30638 : checkPrefixCuts (2^48) 4019716097 9 Manual.Count131072.C030638.packed 128 cuts30638 = true := by
 decide +kernel
def pointBounds30638 : List (Nat × Nat × Nat) := [(4019737600,105495710573772,105496094045539)]
theorem point_links_checked30638 : (cuts30638.take 1).map (fun c => (4019716097-1+2*2^9*c.k,105495639990196+c.lower,105496023461925+c.upper)) = pointBounds30638 := by
 decide +kernel
def cuts30639 : List PrefixCut := [⟨16,50695313,50695342⟩,
⟨128,418300294,418300527⟩]
theorem checked30639 : checkPrefixCuts (2^48) 4019847169 9 Manual.Count131072.C030639.packed 128 cuts30639 = true := by
 decide +kernel
def pointBounds30639 : List (Nat × Nat × Nat) := [(4019863552,105496109069578,105496492541568)]
theorem point_links_checked30639 : (cuts30639.take 1).map (fun c => (4019847169-1+2*2^9*c.k,105496058374265+c.lower,105496441846226+c.upper)) = pointBounds30639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000019
