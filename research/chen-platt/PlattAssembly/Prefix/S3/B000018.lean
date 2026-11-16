import PlattAssemblyKernel
import PlattCertificates.Count131072.C020576
import PlattCertificates.Count131072.C020577
import PlattCertificates.Count131072.C020578
import PlattCertificates.Count131072.C020579
import PlattCertificates.Count131072.C020580
import PlattCertificates.Count131072.C020581
import PlattCertificates.Count131072.C020582
import PlattCertificates.Count131072.C020583
import PlattCertificates.Count131072.C020584
import PlattCertificates.Count131072.C020585
import PlattCertificates.Count131072.C020586
import PlattCertificates.Count131072.C020587
import PlattCertificates.Count131072.C020588
import PlattCertificates.Count131072.C020589
import PlattCertificates.Count131072.C020590
import PlattCertificates.Count131072.C020591
import PlattCertificates.Count131072.C020592
import PlattCertificates.Count131072.C020593
import PlattCertificates.Count131072.C020594
import PlattCertificates.Count131072.C020595
import PlattCertificates.Count131072.C020596
import PlattCertificates.Count131072.C020597
import PlattCertificates.Count131072.C020598
import PlattCertificates.Count131072.C020599
import PlattCertificates.Count131072.C020600
import PlattCertificates.Count131072.C020601
import PlattCertificates.Count131072.C020602
import PlattCertificates.Count131072.C020603
import PlattCertificates.Count131072.C020604
import PlattCertificates.Count131072.C020605
import PlattCertificates.Count131072.C020606
import PlattCertificates.Count131072.C020607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20576 : List PrefixCut := [⟨63,314521305,314521489⟩,
⟨128,634662469,634662838⟩]
theorem checked20576 : checkPrefixCuts (2^48) 2700869633 9 Manual.Count131072.C020576.packed 128 cuts20576 = true := by
 decide +kernel
def pointBounds20576 : List (Nat × Nat × Nat) := [(2700934144,100388860184755,100389240769915)]
theorem point_links_checked20576 : (cuts20576.take 1).map (fun c => (2700869633-1+2*2^9*c.k,100388545663450+c.lower,100388926248426+c.upper)) = pointBounds20576 := by
 decide +kernel
def cuts20577 : List PrefixCut := [⟨18,91914091,91914145⟩,
⟨101,496036600,496036890⟩,
⟨128,627754009,627754377⟩]
theorem checked20577 : checkPrefixCuts (2^48) 2701000705 9 Manual.Count131072.C020577.packed 128 cuts20577 = true := by
 decide +kernel
def pointBounds20577 : List (Nat × Nat × Nat) := [(2701019136,100389272240010,100389652825409),(2701104128,100389676362519,100390056948154)]
theorem point_links_checked20577 : (cuts20577.take 2).map (fun c => (2701000705-1+2*2^9*c.k,100389180325919+c.lower,100389560911264+c.upper)) = pointBounds20577 := by
 decide +kernel
def cuts20578 : List PrefixCut := [⟨56,278227792,278227953⟩,
⟨128,631683128,631683492⟩]
theorem checked20578 : checkPrefixCuts (2^48) 2701131777 9 Manual.Count131072.C020578.packed 128 cuts20578 = true := by
 decide +kernel
def pointBounds20578 : List (Nat × Nat × Nat) := [(2701189120,100390086307720,100390466893594)]
theorem point_links_checked20578 : (cuts20578.take 1).map (fun c => (2701131777-1+2*2^9*c.k,100389808079928+c.lower,100390188665641+c.upper)) = pointBounds20578 := by
 decide +kernel
def cuts20579 : List PrefixCut := [⟨11,57206351,57206383⟩,
⟨94,463583022,463583293⟩,
⟨128,631965112,631965481⟩]
theorem checked20579 : checkPrefixCuts (2^48) 2701262849 9 Manual.Count131072.C020579.packed 128 cuts20579 = true := by
 decide +kernel
def pointBounds20579 : List (Nat × Nat × Nat) := [(2701274112,100390496969407,100390877555516),(2701359104,100390903346078,100391283932426)]
theorem point_links_checked20579 : (cuts20579.take 2).map (fun c => (2701262849-1+2*2^9*c.k,100390439763056+c.lower,100390820349133+c.upper)) = pointBounds20579 := by
 decide +kernel
def cuts20580 : List PrefixCut := [⟨49,237460840,237460979⟩,
⟨128,627454027,627454389⟩]
theorem checked20580 : checkPrefixCuts (2^48) 2701393921 9 Manual.Count131072.C020580.packed 128 cuts20580 = true := by
 decide +kernel
def pointBounds20580 : List (Nat × Nat × Nat) := [(2701444096,100391309189008,100391689775593)]
theorem point_links_checked20580 : (cuts20580.take 1).map (fun c => (2701393921-1+2*2^9*c.k,100391071728168+c.lower,100391452314614+c.upper)) = pointBounds20580 := by
 decide +kernel
def cuts20581 : List PrefixCut := [⟨4,20838208,20838220⟩,
⟨87,429260253,429260504⟩,
⟨128,636383738,636384106⟩]
theorem checked20581 : checkPrefixCuts (2^48) 2701524993 9 Manual.Count131072.C020581.packed 128 cuts20581 = true := by
 decide +kernel
def pointBounds20581 : List (Nat × Nat × Nat) := [(2701529088,100391720020403,100392100607223),(2701614080,100392128442448,100392509029507)]
theorem point_links_checked20581 : (cuts20581.take 2).map (fun c => (2701524993-1+2*2^9*c.k,100391699182195+c.lower,100392079769003+c.upper)) = pointBounds20581 := by
 decide +kernel
def cuts20582 : List PrefixCut := [⟨42,199097967,199098084⟩,
⟨125,609161332,609161687⟩,
⟨128,623329955,623330319⟩]
theorem checked20582 : checkPrefixCuts (2^48) 2701656065 9 Manual.Count131072.C020582.packed 128 cuts20582 = true := by
 decide +kernel
def pointBounds20582 : List (Nat × Nat × Nat) := [(2701699072,100392534663900,100392915251193),(2701784064,100392944727265,100393325314796)]
theorem point_links_checked20582 : (cuts20582.take 2).map (fun c => (2701656065-1+2*2^9*c.k,100392335565933+c.lower,100392716153109+c.upper)) = pointBounds20582 := by
 decide +kernel
def cuts20583 : List PrefixCut := [⟨80,390360359,390360589⟩,
⟨128,625070916,625071282⟩]
theorem checked20583 : checkPrefixCuts (2^48) 2701787137 9 Manual.Count131072.C020583.packed 128 cuts20583 = true := by
 decide +kernel
def pointBounds20583 : List (Nat × Nat × Nat) := [(2701869056,100393349256247,100393729844017)]
theorem point_links_checked20583 : (cuts20583.take 1).map (fun c => (2701787137-1+2*2^9*c.k,100392958895888+c.lower,100393339483428+c.upper)) = pointBounds20583 := by
 decide +kernel
def cuts20584 : List PrefixCut := [⟨35,167826346,167826444⟩,
⟨118,568892141,568892473⟩,
⟨128,618894266,618894627⟩]
theorem checked20584 : checkPrefixCuts (2^48) 2701918209 9 Manual.Count131072.C020584.packed 128 cuts20584 = true := by
 decide +kernel
def pointBounds20584 : List (Nat × Nat × Nat) := [(2701954048,100393751793150,100394132381154),(2702039040,100394152858945,100394533447183)]
theorem point_links_checked20584 : (cuts20584.take 2).map (fun c => (2701918209-1+2*2^9*c.k,100393583966804+c.lower,100393964554710+c.upper)) = pointBounds20584 := by
 decide +kernel
def cuts20585 : List PrefixCut := [⟨73,361155539,361155745⟩,
⟨128,638031200,638031568⟩]
theorem checked20585 : checkPrefixCuts (2^48) 2702049281 9 Manual.Count131072.C020585.packed 128 cuts20585 = true := by
 decide +kernel
def pointBounds20585 : List (Nat × Nat × Nat) := [(2702124032,100394564016609,100394944605082)]
theorem point_links_checked20585 : (cuts20585.take 1).map (fun c => (2702049281-1+2*2^9*c.k,100394202861070+c.lower,100394583449337+c.upper)) = pointBounds20585 := by
 decide +kernel
def cuts20586 : List PrefixCut := [⟨28,138019014,138019098⟩,
⟨111,547796703,547797022⟩,
⟨128,631125603,631125970⟩]
theorem checked20586 : checkPrefixCuts (2^48) 2702180353 9 Manual.Count131072.C020586.packed 128 cuts20586 = true := by
 decide +kernel
def pointBounds20586 : List (Nat × Nat × Nat) := [(2702209024,100394978911284,100395359500003),(2702294016,100395388688973,100395769277927)]
theorem point_links_checked20586 : (cuts20586.take 2).map (fun c => (2702180353-1+2*2^9*c.k,100394840892270+c.lower,100395221480905+c.upper)) = pointBounds20586 := by
 decide +kernel
def cuts20587 : List PrefixCut := [⟨66,319977945,319978133⟩,
⟨128,625470343,625470711⟩]
theorem checked20587 : checkPrefixCuts (2^48) 2702311425 9 Manual.Count131072.C020587.packed 128 cuts20587 = true := by
 decide +kernel
def pointBounds20587 : List (Nat × Nat × Nat) := [(2702379008,100395791995818,100396172585008)]
theorem point_links_checked20587 : (cuts20587.take 1).map (fun c => (2702311425-1+2*2^9*c.k,100395472017873+c.lower,100395852606875+c.upper)) = pointBounds20587 := by
 decide +kernel
def cuts20588 : List PrefixCut := [⟨21,100822357,100822414⟩,
⟨104,516393866,516394166⟩,
⟨128,632105808,632106175⟩]
theorem checked20588 : checkPrefixCuts (2^48) 2702442497 9 Manual.Count131072.C020588.packed 128 cuts20588 = true := by
 decide +kernel
def pointBounds20588 : List (Nat × Nat × Nat) := [(2702464000,100396198310573,100396578900000),(2702548992,100396613882082,100396994471752)]
theorem point_links_checked20588 : (cuts20588.take 2).map (fun c => (2702442497-1+2*2^9*c.k,100396097488216+c.lower,100396478077586+c.upper)) = pointBounds20588 := by
 decide +kernel
def cuts20589 : List PrefixCut := [⟨59,289743948,289744118⟩,
⟨128,630721234,630721599⟩]
theorem checked20589 : checkPrefixCuts (2^48) 2702573569 9 Manual.Count131072.C020589.packed 128 cuts20589 = true := by
 decide +kernel
def pointBounds20589 : List (Nat × Nat × Nat) := [(2702633984,100397019337972,100397399927879)]
theorem point_links_checked20589 : (cuts20589.take 1).map (fun c => (2702573569-1+2*2^9*c.k,100396729594024+c.lower,100397110183761+c.upper)) = pointBounds20589 := by
 decide +kernel
def cuts20590 : List PrefixCut := [⟨14,68944232,68944272⟩,
⟨97,472604238,472604516⟩,
⟨128,624962796,624963159⟩]
theorem checked20590 : checkPrefixCuts (2^48) 2702704641 9 Manual.Count131072.C020590.packed 128 cuts20590 = true := by
 decide +kernel
def pointBounds20590 : List (Nat × Nat × Nat) := [(2702718976,100397429259490,100397809849632),(2702803968,100397832919496,100398213509876)]
theorem point_links_checked20590 : (cuts20590.take 2).map (fun c => (2702704641-1+2*2^9*c.k,100397360315258+c.lower,100397740905360+c.upper)) = pointBounds20590 := by
 decide +kernel
def cuts20591 : List PrefixCut := [⟨52,255558486,255558633⟩,
⟨128,625765611,625765975⟩]
theorem checked20591 : checkPrefixCuts (2^48) 2702835713 9 Manual.Count131072.C020591.packed 128 cuts20591 = true := by
 decide +kernel
def pointBounds20591 : List (Nat × Nat × Nat) := [(2702888960,100398240836540,100398621427152)]
theorem point_links_checked20591 : (cuts20591.take 1).map (fun c => (2702835713-1+2*2^9*c.k,100397985278054+c.lower,100398365868519+c.upper)) = pointBounds20591 := by
 decide +kernel
def cuts20592 : List PrefixCut := [⟨7,36239118,36239139⟩,
⟨90,439548605,439548856⟩,
⟨128,630212892,630213255⟩]
theorem checked20592 : checkPrefixCuts (2^48) 2702966785 9 Manual.Count131072.C020592.packed 128 cuts20592 = true := by
 decide +kernel
def pointBounds20592 : List (Nat × Nat × Nat) := [(2702973952,100398647282783,100399027873633),(2703058944,100399050592270,100399431183350)]
theorem point_links_checked20592 : (cuts20592.take 2).map (fun c => (2702966785-1+2*2^9*c.k,100398611043665+c.lower,100398991634494+c.upper)) = pointBounds20592 := by
 decide +kernel
def cuts20593 : List PrefixCut := [⟨45,227627322,227627459⟩,
⟨128,631119731,631120103⟩]
theorem checked20593 : checkPrefixCuts (2^48) 2703097857 9 Manual.Count131072.C020593.packed 128 cuts20593 = true := by
 decide +kernel
def pointBounds20593 : List (Nat × Nat × Nat) := [(2703143936,100399468883879,100399849475208),(2703228928,100399872376288,100400252967852)]
theorem point_links_checked20593 : (cuts20593.take 2).map (fun c => (2703097857-1+2*2^9*c.k,100399241256557+c.lower,100399621847749+c.upper)) = pointBounds20593 := by
 decide +kernel
def cuts20594 : List PrefixCut := [⟨83,404729225,404729460⟩,
⟨128,624737482,624737846⟩]
theorem checked20594 : checkPrefixCuts (2^48) 2703228929 9 Manual.Count131072.C020594.packed 128 cuts20594 = true := by
 decide +kernel
def pointBounds20594 : List (Nat × Nat × Nat) := [(2703313920,100400277105513,100400657697312)]
theorem point_links_checked20594 : (cuts20594.take 1).map (fun c => (2703228929-1+2*2^9*c.k,100399872376288+c.lower,100400252967852+c.upper)) = pointBounds20594 := by
 decide +kernel
def cuts20595 : List PrefixCut := [⟨38,187935941,187936053⟩,
⟨121,593993183,593993533⟩,
⟨128,630329487,630329857⟩]
theorem checked20595 : checkPrefixCuts (2^48) 2703360001 9 Manual.Count131072.C020595.packed 128 cuts20595 = true := by
 decide +kernel
def pointBounds20595 : List (Nat × Nat × Nat) := [(2703398912,100400685049711,100401065641751),(2703483904,100401091106953,100401471699231)]
theorem point_links_checked20595 : (cuts20595.take 2).map (fun c => (2703360001-1+2*2^9*c.k,100400497113770+c.lower,100400877705698+c.upper)) = pointBounds20595 := by
 decide +kernel
def cuts20596 : List PrefixCut := [⟨76,383555389,383555607⟩,
⟨128,636337661,636338026⟩]
theorem checked20596 : checkPrefixCuts (2^48) 2703491073 9 Manual.Count131072.C020596.packed 128 cuts20596 = true := by
 decide +kernel
def pointBounds20596 : List (Nat × Nat × Nat) := [(2703568896,100401510998646,100401891591162)]
theorem point_links_checked20596 : (cuts20596.take 1).map (fun c => (2703491073-1+2*2^9*c.k,100401127443257+c.lower,100401508035555+c.upper)) = pointBounds20596 := by
 decide +kernel
def cuts20597 : List PrefixCut := [⟨31,150022061,150022147⟩,
⟨114,557498553,557498874⟩,
⟨128,624021984,624022344⟩]
theorem checked20597 : checkPrefixCuts (2^48) 2703622145 9 Manual.Count131072.C020597.packed 128 cuts20597 = true := by
 decide +kernel
def pointBounds20597 : List (Nat × Nat × Nat) := [(2703653888,100401913802979,100402294395728),(2703738880,100402321279471,100402701872455)]
theorem point_links_checked20597 : (cuts20597.take 2).map (fun c => (2703622145-1+2*2^9*c.k,100401763780918+c.lower,100402144373581+c.upper)) = pointBounds20597 := by
 decide +kernel
def cuts20598 : List PrefixCut := [⟨69,341044278,341044475⟩,
⟨128,624928675,624929040⟩]
theorem checked20598 : checkPrefixCuts (2^48) 2703753217 9 Manual.Count131072.C020598.packed 128 cuts20598 = true := by
 decide +kernel
def pointBounds20598 : List (Nat × Nat × Nat) := [(2703823872,100402728847180,100403109440400)]
theorem point_links_checked20598 : (cuts20598.take 1).map (fun c => (2703753217-1+2*2^9*c.k,100402387802902+c.lower,100402768395925+c.upper)) = pointBounds20598 := by
 decide +kernel
def cuts20599 : List PrefixCut := [⟨24,116487591,116487661⟩,
⟨107,519761731,519762039⟩,
⟨128,622191777,622192144⟩]
theorem checked20599 : checkPrefixCuts (2^48) 2703884289 9 Manual.Count131072.C020599.packed 128 cuts20599 = true := by
 decide +kernel
def pointBounds20599 : List (Nat × Nat × Nat) := [(2703908864,100403129219168,100403509812626),(2703993856,100403532493308,100403913087004)]
theorem point_links_checked20599 : (cuts20599.take 2).map (fun c => (2703884289-1+2*2^9*c.k,100403012731577+c.lower,100403393324965+c.upper)) = pointBounds20599 := by
 decide +kernel
def cuts20600 : List PrefixCut := [⟨62,305723913,305724084⟩,
⟨128,623619057,623619406⟩]
theorem checked20600 : checkPrefixCuts (2^48) 2704015361 9 Manual.Count131072.C020600.packed 128 cuts20600 = true := by
 decide +kernel
def pointBounds20600 : List (Nat × Nat × Nat) := [(2704078848,100403940647267,100404321241193)]
theorem point_links_checked20600 : (cuts20600.take 1).map (fun c => (2704015361-1+2*2^9*c.k,100403634923354+c.lower,100404015517109+c.upper)) = pointBounds20600 := by
 decide +kernel
def cuts20601 : List PrefixCut := [⟨17,81918650,81918698⟩,
⟨100,493793997,493794282⟩,
⟨128,622756068,622756426⟩]
theorem checked20601 : checkPrefixCuts (2^48) 2704146433 9 Manual.Count131072.C020601.packed 128 cuts20601 = true := by
 decide +kernel
def pointBounds20601 : List (Nat × Nat × Nat) := [(2704163840,100404340461061,100404721055213),(2704248832,100404752336408,100405132930797)]
theorem point_links_checked20601 : (cuts20601.take 2).map (fun c => (2704146433-1+2*2^9*c.k,100404258542411+c.lower,100404639136515+c.upper)) = pointBounds20601 := by
 decide +kernel
def cuts20602 : List PrefixCut := [⟨55,273844965,273845118⟩,
⟨128,627721964,627722332⟩]
theorem checked20602 : checkPrefixCuts (2^48) 2704277505 9 Manual.Count131072.C020602.packed 128 cuts20602 = true := by
 decide +kernel
def pointBounds20602 : List (Nat × Nat × Nat) := [(2704333824,100405155143444,100405535738059)]
theorem point_links_checked20602 : (cuts20602.take 1).map (fun c => (2704277505-1+2*2^9*c.k,100404881298479+c.lower,100405261892941+c.upper)) = pointBounds20602 := by
 decide +kernel
def cuts20603 : List PrefixCut := [⟨10,48917516,48917544⟩,
⟨93,462523453,462523722⟩,
⟨128,632687138,632687510⟩]
theorem checked20603 : checkPrefixCuts (2^48) 2704408577 9 Manual.Count131072.C020603.packed 128 cuts20603 = true := by
 decide +kernel
def pointBounds20603 : List (Nat × Nat × Nat) := [(2704418816,100405557937959,100405938532817),(2704503808,100405971543896,100406352138995)]
theorem point_links_checked20603 : (cuts20603.take 2).map (fun c => (2704408577-1+2*2^9*c.k,100405509020443+c.lower,100405889615273+c.upper)) = pointBounds20603 := by
 decide +kernel
def cuts20604 : List PrefixCut := [⟨48,235623608,235623745⟩,
⟨128,623289993,623290362⟩]
theorem checked20604 : checkPrefixCuts (2^48) 2704539649 9 Manual.Count131072.C020604.packed 128 cuts20604 = true := by
 decide +kernel
def pointBounds20604 : List (Nat × Nat × Nat) := [(2704588800,100406377331189,100406757926528)]
theorem point_links_checked20604 : (cuts20604.take 1).map (fun c => (2704539649-1+2*2^9*c.k,100406141707581+c.lower,100406522302783+c.upper)) = pointBounds20604 := by
 decide +kernel
def cuts20605 : List PrefixCut := [⟨3,14777921,14777930⟩,
⟨86,423557761,423558014⟩,
⟨128,627110301,627110676⟩]
theorem checked20605 : checkPrefixCuts (2^48) 2704670721 9 Manual.Count131072.C020605.packed 128 cuts20605 = true := by
 decide +kernel
def pointBounds20605 : List (Nat × Nat × Nat) := [(2704673792,100406779775495,100407160371075),(2704758784,100407188555335,100407569151159)]
theorem point_links_checked20605 : (cuts20605.take 2).map (fun c => (2704670721-1+2*2^9*c.k,100406764997574+c.lower,100407145593145+c.upper)) = pointBounds20605 := by
 decide +kernel
def cuts20606 : List PrefixCut := [⟨41,202092439,202092560⟩,
⟨124,612719680,612720047⟩,
⟨128,631658585,631658963⟩]
theorem checked20606 : checkPrefixCuts (2^48) 2704801793 9 Manual.Count131072.C020606.packed 128 cuts20606 = true := by
 decide +kernel
def pointBounds20606 : List (Nat × Nat × Nat) := [(2704843776,100407594200314,100407974796381),(2704928768,100408004827555,100408385423868)]
theorem point_links_checked20606 : (cuts20606.take 2).map (fun c => (2704801793-1+2*2^9*c.k,100407392107875+c.lower,100407772703821+c.upper)) = pointBounds20606 := by
 decide +kernel
def cuts20607 : List PrefixCut := [⟨79,389594210,389594442⟩,
⟨128,629858997,629859371⟩]
theorem checked20607 : checkPrefixCuts (2^48) 2704932865 9 Manual.Count131072.C020607.packed 128 cuts20607 = true := by
 decide +kernel
def pointBounds20607 : List (Nat × Nat × Nat) := [(2705013760,100408413360670,100408793957226)]
theorem point_links_checked20607 : (cuts20607.take 1).map (fun c => (2704932865-1+2*2^9*c.k,100408023766460+c.lower,100408404362784+c.upper)) = pointBounds20607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000018
