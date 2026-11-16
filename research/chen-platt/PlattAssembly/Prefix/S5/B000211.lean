import PlattAssemblyKernel
import PlattCertificates.Count131072.C046752
import PlattCertificates.Count131072.C046753
import PlattCertificates.Count131072.C046754
import PlattCertificates.Count131072.C046755
import PlattCertificates.Count131072.C046756
import PlattCertificates.Count131072.C046757
import PlattCertificates.Count131072.C046758
import PlattCertificates.Count131072.C046759
import PlattCertificates.Count131072.C046760
import PlattCertificates.Count131072.C046761
import PlattCertificates.Count131072.C046762
import PlattCertificates.Count131072.C046763
import PlattCertificates.Count131072.C046764
import PlattCertificates.Count131072.C046765
import PlattCertificates.Count131072.C046766
import PlattCertificates.Count131072.C046767
import PlattCertificates.Count131072.C046768
import PlattCertificates.Count131072.C046769
import PlattCertificates.Count131072.C046770
import PlattCertificates.Count131072.C046771
import PlattCertificates.Count131072.C046772
import PlattCertificates.Count131072.C046773
import PlattCertificates.Count131072.C046774
import PlattCertificates.Count131072.C046775
import PlattCertificates.Count131072.C046776
import PlattCertificates.Count131072.C046777
import PlattCertificates.Count131072.C046778
import PlattCertificates.Count131072.C046779
import PlattCertificates.Count131072.C046780
import PlattCertificates.Count131072.C046781
import PlattCertificates.Count131072.C046782
import PlattCertificates.Count131072.C046783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000211
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46752 : List PrefixCut := [⟨42,173975119,173975217⟩,
⟨64,266883265,266883417⟩]
theorem checked46752 : checkPrefixCuts (2^48) 6131810305 10 Manual.Count131072.C046752.packed 64 cuts46752 = true := by
 decide +kernel
def pointBounds46752 : List (Nat × Nat × Nat) := [(6131896320,110819949823746,110820336467526)]
theorem point_links_checked46752 : (cuts46752.take 1).map (fun c => (6131810305-1+2*2^10*c.k,110819775848627+c.lower,110820162492309+c.upper)) = pointBounds46752 := by
 decide +kernel
def cuts46753 : List PrefixCut := [⟨64,268346455,268346602⟩]
theorem checked46753 : checkPrefixCuts (2^48) 6131941377 10 Manual.Count131072.C046753.packed 64 cuts46753 = true := by
 decide +kernel
def cuts46754 : List PrefixCut := [⟨8,33049457,33049475⟩,
⟨64,266596446,266596594⟩]
theorem checked46754 : checkPrefixCuts (2^48) 6132072449 10 Manual.Count131072.C046754.packed 64 cuts46754 = true := by
 decide +kernel
def pointBounds46754 : List (Nat × Nat × Nat) := [(6132088832,110820344127804,110820730771803)]
theorem point_links_checked46754 : (cuts46754.take 1).map (fun c => (6132072449-1+2*2^10*c.k,110820311078347+c.lower,110820697722328+c.upper)) = pointBounds46754 := by
 decide +kernel
def cuts46755 : List PrefixCut := [⟨38,157715177,157715272⟩,
⟨64,267784144,267784301⟩]
theorem checked46755 : checkPrefixCuts (2^48) 6132203521 10 Manual.Count131072.C046755.packed 64 cuts46755 = true := by
 decide +kernel
def pointBounds46755 : List (Nat × Nat × Nat) := [(6132281344,110820735389970,110821122034194)]
theorem point_links_checked46755 : (cuts46755.take 1).map (fun c => (6132203521-1+2*2^10*c.k,110820577674793+c.lower,110820964318922+c.upper)) = pointBounds46755 := by
 decide +kernel
def cuts46756 : List PrefixCut := [⟨64,271358611,271358764⟩]
theorem checked46756 : checkPrefixCuts (2^48) 6132334593 10 Manual.Count131072.C046756.packed 64 cuts46756 = true := by
 decide +kernel
def cuts46757 : List PrefixCut := [⟨4,15972890,15972899⟩,
⟨64,267221934,267222085⟩]
theorem checked46757 : checkPrefixCuts (2^48) 6132465665 10 Manual.Count131072.C046757.packed 64 cuts46757 = true := by
 decide +kernel
def pointBounds46757 : List (Nat × Nat × Nat) := [(6132473856,110821132790438,110821519434886)]
theorem point_links_checked46757 : (cuts46757.take 1).map (fun c => (6132465665-1+2*2^10*c.k,110821116817548+c.lower,110821503461987+c.upper)) = pointBounds46757 := by
 decide +kernel
def cuts46758 : List PrefixCut := [⟨34,145037358,145037441⟩,
⟨64,271668311,271668463⟩]
theorem checked46758 : checkPrefixCuts (2^48) 6132596737 10 Manual.Count131072.C046758.packed 64 cuts46758 = true := by
 decide +kernel
def pointBounds46758 : List (Nat × Nat × Nat) := [(6132666368,110821529076840,110821915721513)]
theorem point_links_checked46758 : (cuts46758.take 1).map (fun c => (6132596737-1+2*2^10*c.k,110821384039482+c.lower,110821770684072+c.upper)) = pointBounds46758 := by
 decide +kernel
def cuts46759 : List PrefixCut := [⟨64,267164621,267164771⟩]
theorem checked46759 : checkPrefixCuts (2^48) 6132727809 10 Manual.Count131072.C046759.packed 64 cuts46759 = true := by
 decide +kernel
def pointBounds46759 : List (Nat × Nat × Nat) := [(6132858880,110821922872414,110822309517306)]
theorem point_links_checked46759 : (cuts46759.take 1).map (fun c => (6132727809-1+2*2^10*c.k,110821655707793+c.lower,110822042352535+c.upper)) = pointBounds46759 := by
 decide +kernel
def cuts46760 : List PrefixCut := [⟨64,267342483,267342637⟩]
theorem checked46760 : checkPrefixCuts (2^48) 6132858881 10 Manual.Count131072.C046760.packed 64 cuts46760 = true := by
 decide +kernel
def cuts46761 : List PrefixCut := [⟨30,125109738,125109810⟩,
⟨64,264307738,264307888⟩]
theorem checked46761 : checkPrefixCuts (2^48) 6132989953 10 Manual.Count131072.C046761.packed 64 cuts46761 = true := by
 decide +kernel
def pointBounds46761 : List (Nat × Nat × Nat) := [(6133051392,110822315324635,110822701969753)]
theorem point_links_checked46761 : (cuts46761.take 1).map (fun c => (6132989953-1+2*2^10*c.k,110822190214897+c.lower,110822576859943+c.upper)) = pointBounds46761 := by
 decide +kernel
def cuts46762 : List PrefixCut := [⟨60,250855366,250855512⟩,
⟨64,267652308,267652465⟩]
theorem checked46762 : checkPrefixCuts (2^48) 6133121025 10 Manual.Count131072.C046762.packed 64 cuts46762 = true := by
 decide +kernel
def pointBounds46762 : List (Nat × Nat × Nat) := [(6133243904,110822705378001,110823092023343)]
theorem point_links_checked46762 : (cuts46762.take 1).map (fun c => (6133121025-1+2*2^10*c.k,110822454522635+c.lower,110822841167831+c.upper)) = pointBounds46762 := by
 decide +kernel
def cuts46763 : List PrefixCut := [⟨64,265306076,265306232⟩]
theorem checked46763 : checkPrefixCuts (2^48) 6133252097 10 Manual.Count131072.C046763.packed 64 cuts46763 = true := by
 decide +kernel
def cuts46764 : List PrefixCut := [⟨26,108351188,108351251⟩,
⟨64,266034656,266034814⟩]
theorem checked46764 : checkPrefixCuts (2^48) 6133383169 10 Manual.Count131072.C046764.packed 64 cuts46764 = true := by
 decide +kernel
def pointBounds46764 : List (Nat × Nat × Nat) := [(6133436416,110823095832207,110823482477779)]
theorem point_links_checked46764 : (cuts46764.take 1).map (fun c => (6133383169-1+2*2^10*c.k,110822987481019+c.lower,110823374126528+c.upper)) = pointBounds46764 := by
 decide +kernel
def cuts46765 : List PrefixCut := [⟨56,230463918,230464046⟩,
⟨64,264376903,264377051⟩]
theorem checked46765 : checkPrefixCuts (2^48) 6133514241 10 Manual.Count131072.C046765.packed 64 cuts46765 = true := by
 decide +kernel
def pointBounds46765 : List (Nat × Nat × Nat) := [(6133628928,110823483979593,110823870625388)]
theorem point_links_checked46765 : (cuts46765.take 1).map (fun c => (6133514241-1+2*2^10*c.k,110823253515675+c.lower,110823640161342+c.upper)) = pointBounds46765 := by
 decide +kernel
def cuts46766 : List PrefixCut := [⟨64,266482181,266482333⟩]
theorem checked46766 : checkPrefixCuts (2^48) 6133645313 10 Manual.Count131072.C046766.packed 64 cuts46766 = true := by
 decide +kernel
def cuts46767 : List PrefixCut := [⟨22,91548873,91548925⟩,
⟨64,267302491,267302647⟩]
theorem checked46767 : checkPrefixCuts (2^48) 6133776385 10 Manual.Count131072.C046767.packed 64 cuts46767 = true := by
 decide +kernel
def pointBounds46767 : List (Nat × Nat × Nat) := [(6133821440,110823875923632,110824262569651)]
theorem point_links_checked46767 : (cuts46767.take 1).map (fun c => (6133776385-1+2*2^10*c.k,110823784374759+c.lower,110824171020726+c.upper)) = pointBounds46767 := by
 decide +kernel
def cuts46768 : List PrefixCut := [⟨52,218518448,218518573⟩,
⟨64,270141847,270141999⟩]
theorem checked46768 : checkPrefixCuts (2^48) 6133907457 10 Manual.Count131072.C046768.packed 64 cuts46768 = true := by
 decide +kernel
def pointBounds46768 : List (Nat × Nat × Nat) := [(6134013952,110824270195698,110824656841946)]
theorem point_links_checked46768 : (cuts46768.take 1).map (fun c => (6133907457-1+2*2^10*c.k,110824051677250+c.lower,110824438323373+c.upper)) = pointBounds46768 := by
 decide +kernel
def cuts46769 : List PrefixCut := [⟨64,263803665,263803821⟩]
theorem checked46769 : checkPrefixCuts (2^48) 6134038529 10 Manual.Count131072.C046769.packed 64 cuts46769 = true := by
 decide +kernel
def cuts46770 : List PrefixCut := [⟨18,75069912,75069954⟩,
⟨64,263798060,263798210⟩]
theorem checked46770 : checkPrefixCuts (2^48) 6134169601 10 Manual.Count131072.C046770.packed 64 cuts46770 = true := by
 decide +kernel
def pointBounds46770 : List (Nat × Nat × Nat) := [(6134206464,110824660692674,110825047339147)]
theorem point_links_checked46770 : (cuts46770.take 1).map (fun c => (6134169601-1+2*2^10*c.k,110824585622762+c.lower,110824972269193+c.upper)) = pointBounds46770 := by
 decide +kernel
def cuts46771 : List PrefixCut := [⟨48,202490695,202490806⟩,
⟨64,268426795,268426943⟩]
theorem checked46771 : checkPrefixCuts (2^48) 6134300673 10 Manual.Count131072.C046771.packed 64 cuts46771 = true := by
 decide +kernel
def pointBounds46771 : List (Nat × Nat × Nat) := [(6134398976,110825051911517,110825438558209)]
theorem point_links_checked46771 : (cuts46771.take 1).map (fun c => (6134300673-1+2*2^10*c.k,110824849420822+c.lower,110825236067403+c.upper)) = pointBounds46771 := by
 decide +kernel
def cuts46772 : List PrefixCut := [⟨64,262364361,262364509⟩]
theorem checked46772 : checkPrefixCuts (2^48) 6134431745 10 Manual.Count131072.C046772.packed 64 cuts46772 = true := by
 decide +kernel
def cuts46773 : List PrefixCut := [⟨14,57904772,57904807⟩,
⟨64,268461176,268461335⟩]
theorem checked46773 : checkPrefixCuts (2^48) 6134562817 10 Manual.Count131072.C046773.packed 64 cuts46773 = true := by
 decide +kernel
def pointBounds46773 : List (Nat × Nat × Nat) := [(6134591488,110825438116750,110825824763662)]
theorem point_links_checked46773 : (cuts46773.take 1).map (fun c => (6134562817-1+2*2^10*c.k,110825380211978+c.lower,110825766858855+c.upper)) = pointBounds46773 := by
 decide +kernel
def cuts46774 : List PrefixCut := [⟨44,185455576,185455677⟩,
⟨64,272171879,272172027⟩]
theorem checked46774 : checkPrefixCuts (2^48) 6134693889 10 Manual.Count131072.C046774.packed 64 cuts46774 = true := by
 decide +kernel
def pointBounds46774 : List (Nat × Nat × Nat) := [(6134784000,110825834128730,110826220775867)]
theorem point_links_checked46774 : (cuts46774.take 1).map (fun c => (6134693889-1+2*2^10*c.k,110825648673154+c.lower,110826035320190+c.upper)) = pointBounds46774 := by
 decide +kernel
def cuts46775 : List PrefixCut := [⟨64,267807372,267807528⟩]
theorem checked46775 : checkPrefixCuts (2^48) 6134824961 10 Manual.Count131072.C046775.packed 64 cuts46775 = true := by
 decide +kernel
def cuts46776 : List PrefixCut := [⟨10,42714681,42714704⟩,
⟨64,266195875,266196029⟩]
theorem checked46776 : checkPrefixCuts (2^48) 6134956033 10 Manual.Count131072.C046776.packed 64 cuts46776 = true := by
 decide +kernel
def pointBounds46776 : List (Nat × Nat × Nat) := [(6134976512,110826231367086,110826618014449)]
theorem point_links_checked46776 : (cuts46776.take 1).map (fun c => (6134956033-1+2*2^10*c.k,110826188652405+c.lower,110826575299745+c.upper)) = pointBounds46776 := by
 decide +kernel
def cuts46777 : List PrefixCut := [⟨40,169982512,169982608⟩,
⟨64,270273421,270273573⟩]
theorem checked46777 : checkPrefixCuts (2^48) 6135087105 10 Manual.Count131072.C046777.packed 64 cuts46777 = true := by
 decide +kernel
def pointBounds46777 : List (Nat × Nat × Nat) := [(6135169024,110826624830792,110827011478382)]
theorem point_links_checked46777 : (cuts46777.take 1).map (fun c => (6135087105-1+2*2^10*c.k,110826454848280+c.lower,110826841495774+c.upper)) = pointBounds46777 := by
 decide +kernel
def cuts46778 : List PrefixCut := [⟨64,271781637,271781790⟩]
theorem checked46778 : checkPrefixCuts (2^48) 6135218177 10 Manual.Count131072.C046778.packed 64 cuts46778 = true := by
 decide +kernel
def cuts46779 : List PrefixCut := [⟨6,24452718,24452733⟩,
⟨64,264573125,264573273⟩]
theorem checked46779 : checkPrefixCuts (2^48) 6135349249 10 Manual.Count131072.C046779.packed 64 cuts46779 = true := by
 decide +kernel
def pointBounds46779 : List (Nat × Nat × Nat) := [(6135361536,110827021356056,110827408003870)]
theorem point_links_checked46779 : (cuts46779.take 1).map (fun c => (6135349249-1+2*2^10*c.k,110826996903338+c.lower,110827383551137+c.upper)) = pointBounds46779 := by
 decide +kernel
def cuts46780 : List PrefixCut := [⟨36,149006261,149006347⟩,
⟨64,263099426,263099577⟩]
theorem checked46780 : checkPrefixCuts (2^48) 6135480321 10 Manual.Count131072.C046780.packed 64 cuts46780 = true := by
 decide +kernel
def pointBounds46780 : List (Nat × Nat × Nat) := [(6135554048,110827410482724,110827797130757)]
theorem point_links_checked46780 : (cuts46780.take 1).map (fun c => (6135480321-1+2*2^10*c.k,110827261476463+c.lower,110827648124410+c.upper)) = pointBounds46780 := by
 decide +kernel
def cuts46781 : List PrefixCut := [⟨64,264745273,264745426⟩]
theorem checked46781 : checkPrefixCuts (2^48) 6135611393 10 Manual.Count131072.C046781.packed 64 cuts46781 = true := by
 decide +kernel
def cuts46782 : List PrefixCut := [⟨2,7477561,7477566⟩,
⟨64,268134339,268134488⟩]
theorem checked46782 : checkPrefixCuts (2^48) 6135742465 10 Manual.Count131072.C046782.packed 64 cuts46782 = true := by
 decide +kernel
def pointBounds46782 : List (Nat × Nat × Nat) := [(6135746560,110827796798723,110828183446979)]
theorem point_links_checked46782 : (cuts46782.take 1).map (fun c => (6135742465-1+2*2^10*c.k,110827789321162+c.lower,110828175969413+c.upper)) = pointBounds46782 := by
 decide +kernel
def cuts46783 : List PrefixCut := [⟨32,132574136,132574209⟩,
⟨64,265422088,265422236⟩]
theorem checked46783 : checkPrefixCuts (2^48) 6135873537 10 Manual.Count131072.C046783.packed 64 cuts46783 = true := by
 decide +kernel
def pointBounds46783 : List (Nat × Nat × Nat) := [(6135939072,110828190029637,110828576678110)]
theorem point_links_checked46783 : (cuts46783.take 1).map (fun c => (6135873537-1+2*2^10*c.k,110828057455501+c.lower,110828444103901+c.upper)) = pointBounds46783 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000211
