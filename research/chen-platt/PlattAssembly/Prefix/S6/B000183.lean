import PlattAssemblyKernel
import PlattCertificates.Count131072.C055856
import PlattCertificates.Count131072.C055857
import PlattCertificates.Count131072.C055858
import PlattCertificates.Count131072.C055859
import PlattCertificates.Count131072.C055860
import PlattCertificates.Count131072.C055861
import PlattCertificates.Count131072.C055862
import PlattCertificates.Count131072.C055863
import PlattCertificates.Count131072.C055864
import PlattCertificates.Count131072.C055865
import PlattCertificates.Count131072.C055866
import PlattCertificates.Count131072.C055867
import PlattCertificates.Count131072.C055868
import PlattCertificates.Count131072.C055869
import PlattCertificates.Count131072.C055870
import PlattCertificates.Count131072.C055871
import PlattCertificates.Count131072.C055872
import PlattCertificates.Count131072.C055873
import PlattCertificates.Count131072.C055874
import PlattCertificates.Count131072.C055875
import PlattCertificates.Count131072.C055876
import PlattCertificates.Count131072.C055877
import PlattCertificates.Count131072.C055878
import PlattCertificates.Count131072.C055879
import PlattCertificates.Count131072.C055880
import PlattCertificates.Count131072.C055881
import PlattCertificates.Count131072.C055882
import PlattCertificates.Count131072.C055883
import PlattCertificates.Count131072.C055884
import PlattCertificates.Count131072.C055885
import PlattCertificates.Count131072.C055886
import PlattCertificates.Count131072.C055887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55856 : List PrefixCut := [⟨64,220295069,220295195⟩]
theorem checked55856 : checkPrefixCuts (2^48) 7325089793 10 Manual.Count131072.C055856.packed 64 cuts55856 = true := by
 decide +kernel
def cuts55857 : List PrefixCut := [⟨25,87993967,87994018⟩,
⟨64,222788759,222788887⟩]
theorem checked55857 : checkPrefixCuts (2^48) 7325220865 10 Manual.Count131072.C055857.packed 64 cuts55857 = true := by
 decide +kernel
def pointBounds55857 : List (Nat × Nat × Nat) := [(7325272064,113032136322418,113032524225811)]
theorem point_links_checked55857 : (cuts55857.take 1).map (fun c => (7325220865-1+2*2^10*c.k,113032048328451+c.lower,113032436231793+c.upper)) = pointBounds55857 := by
 decide +kernel
def cuts55858 : List PrefixCut := [⟨64,219864497,219864623⟩]
theorem checked55858 : checkPrefixCuts (2^48) 7325351937 10 Manual.Count131072.C055858.packed 64 cuts55858 = true := by
 decide +kernel
def cuts55859 : List PrefixCut := [⟨9,30854490,30854509⟩,
⟨64,219245799,219245924⟩]
theorem checked55859 : checkPrefixCuts (2^48) 7325483009 10 Manual.Count131072.C055859.packed 64 cuts55859 = true := by
 decide +kernel
def pointBounds55859 : List (Nat × Nat × Nat) := [(7325501440,113032521836197,113032909739812)]
theorem point_links_checked55859 : (cuts55859.take 1).map (fun c => (7325483009-1+2*2^10*c.k,113032490981707+c.lower,113032878885303+c.upper)) = pointBounds55859 := by
 decide +kernel
def cuts55860 : List PrefixCut := [⟨57,197379357,197379471⟩,
⟨64,222046754,222046881⟩]
theorem checked55860 : checkPrefixCuts (2^48) 7325614081 10 Manual.Count131072.C055860.packed 64 cuts55860 = true := by
 decide +kernel
def pointBounds55860 : List (Nat × Nat × Nat) := [(7325730816,113032907606863,113033295510698)]
theorem point_links_checked55860 : (cuts55860.take 1).map (fun c => (7325614081-1+2*2^10*c.k,113032710227506+c.lower,113033098131227+c.upper)) = pointBounds55860 := by
 decide +kernel
def cuts55861 : List PrefixCut := [⟨64,222081220,222081345⟩]
theorem checked55861 : checkPrefixCuts (2^48) 7325745153 10 Manual.Count131072.C055861.packed 64 cuts55861 = true := by
 decide +kernel
def cuts55862 : List PrefixCut := [⟨41,143082747,143082829⟩,
⟨64,222461457,222461584⟩]
theorem checked55862 : checkPrefixCuts (2^48) 7325876225 10 Manual.Count131072.C055862.packed 64 cuts55862 = true := by
 decide +kernel
def pointBounds55862 : List (Nat × Nat × Nat) := [(7325960192,113033297438227,113033685342282)]
theorem point_links_checked55862 : (cuts55862.take 1).map (fun c => (7325876225-1+2*2^10*c.k,113033154355480+c.lower,113033542259453+c.upper)) = pointBounds55862 := by
 decide +kernel
def cuts55863 : List PrefixCut := [⟨64,222150114,222150242⟩]
theorem checked55863 : checkPrefixCuts (2^48) 7326007297 10 Manual.Count131072.C055863.packed 64 cuts55863 = true := by
 decide +kernel
def cuts55864 : List PrefixCut := [⟨25,86868758,86868809⟩,
⟨64,223145060,223145187⟩]
theorem checked55864 : checkPrefixCuts (2^48) 7326138369 10 Manual.Count131072.C055864.packed 64 cuts55864 = true := by
 decide +kernel
def pointBounds55864 : List (Nat × Nat × Nat) := [(7326189568,113033685835809,113034073740088)]
theorem point_links_checked55864 : (cuts55864.take 1).map (fun c => (7326138369-1+2*2^10*c.k,113033598967051+c.lower,113033986871279+c.upper)) = pointBounds55864 := by
 decide +kernel
def cuts55865 : List PrefixCut := [⟨64,219337538,219337663⟩]
theorem checked55865 : checkPrefixCuts (2^48) 7326269441 10 Manual.Count131072.C055865.packed 64 cuts55865 = true := by
 decide +kernel
def cuts55866 : List PrefixCut := [⟨9,30504855,30504874⟩,
⟨64,222676029,222676157⟩]
theorem checked55866 : checkPrefixCuts (2^48) 7326400513 10 Manual.Count131072.C055866.packed 64 cuts55866 = true := by
 decide +kernel
def pointBounds55866 : List (Nat × Nat × Nat) := [(7326418944,113034071954504,113034459859003)]
theorem point_links_checked55866 : (cuts55866.take 1).map (fun c => (7326400513-1+2*2^10*c.k,113034041449649+c.lower,113034429354129+c.upper)) = pointBounds55866 := by
 decide +kernel
def cuts55867 : List PrefixCut := [⟨57,198391946,198392056⟩,
⟨64,223171507,223171631⟩]
theorem checked55867 : checkPrefixCuts (2^48) 7326531585 10 Manual.Count131072.C055867.packed 64 cuts55867 = true := by
 decide +kernel
def pointBounds55867 : List (Nat × Nat × Nat) := [(7326648320,113034462517624,113034850422342)]
theorem point_links_checked55867 : (cuts55867.take 1).map (fun c => (7326531585-1+2*2^10*c.k,113034264125678+c.lower,113034652030286+c.upper)) = pointBounds55867 := by
 decide +kernel
def cuts55868 : List PrefixCut := [⟨64,218864759,218864884⟩]
theorem checked55868 : checkPrefixCuts (2^48) 7326662657 10 Manual.Count131072.C055868.packed 64 cuts55868 = true := by
 decide +kernel
def cuts55869 : List PrefixCut := [⟨41,143064825,143064906⟩,
⟨64,221473179,221473305⟩]
theorem checked55869 : checkPrefixCuts (2^48) 7326793729 10 Manual.Count131072.C055869.packed 64 cuts55869 = true := by
 decide +kernel
def pointBounds55869 : List (Nat × Nat × Nat) := [(7326877696,113034849226769,113035237131707)]
theorem point_links_checked55869 : (cuts55869.take 1).map (fun c => (7326793729-1+2*2^10*c.k,113034706161944+c.lower,113035094066801+c.upper)) = pointBounds55869 := by
 decide +kernel
def cuts55870 : List PrefixCut := [⟨64,224388835,224388963⟩]
theorem checked55870 : checkPrefixCuts (2^48) 7326924801 10 Manual.Count131072.C055870.packed 64 cuts55870 = true := by
 decide +kernel
def cuts55871 : List PrefixCut := [⟨25,87472528,87472577⟩,
⟨64,223117121,223117245⟩]
theorem checked55871 : checkPrefixCuts (2^48) 7327055873 10 Manual.Count131072.C055871.packed 64 cuts55871 = true := by
 decide +kernel
def pointBounds55871 : List (Nat × Nat × Nat) := [(7327107072,113035239496486,113035627401646)]
theorem point_links_checked55871 : (cuts55871.take 1).map (fun c => (7327055873-1+2*2^10*c.k,113035152023958+c.lower,113035539929069+c.upper)) = pointBounds55871 := by
 decide +kernel
def cuts55872 : List PrefixCut := [⟨64,221230791,221230919⟩]
theorem checked55872 : checkPrefixCuts (2^48) 7327186945 10 Manual.Count131072.C055872.packed 64 cuts55872 = true := by
 decide +kernel
def cuts55873 : List PrefixCut := [⟨9,30270549,30270566⟩,
⟨64,223185957,223186083⟩]
theorem checked55873 : checkPrefixCuts (2^48) 7327318017 10 Manual.Count131072.C055873.packed 64 cuts55873 = true := by
 decide +kernel
def pointBounds55873 : List (Nat × Nat × Nat) := [(7327336448,113035626642419,113036014547799)]
theorem point_links_checked55873 : (cuts55873.take 1).map (fun c => (7327318017-1+2*2^10*c.k,113035596371870+c.lower,113035984277233+c.upper)) = pointBounds55873 := by
 decide +kernel
def cuts55874 : List PrefixCut := [⟨57,198021386,198021498⟩,
⟨64,221952757,221952883⟩]
theorem checked55874 : checkPrefixCuts (2^48) 7327449089 10 Manual.Count131072.C055874.packed 64 cuts55874 = true := by
 decide +kernel
def pointBounds55874 : List (Nat × Nat × Nat) := [(7327565824,113036017579213,113036405484814)]
theorem point_links_checked55874 : (cuts55874.take 1).map (fun c => (7327449089-1+2*2^10*c.k,113035819557827+c.lower,113036207463316+c.upper)) = pointBounds55874 := by
 decide +kernel
def cuts55875 : List PrefixCut := [⟨64,220143362,220143489⟩]
theorem checked55875 : checkPrefixCuts (2^48) 7327580161 10 Manual.Count131072.C055875.packed 64 cuts55875 = true := by
 decide +kernel
def cuts55876 : List PrefixCut := [⟨41,141702487,141702567⟩,
⟨64,221714324,221714448⟩]
theorem checked55876 : checkPrefixCuts (2^48) 7327711233 10 Manual.Count131072.C055876.packed 64 cuts55876 = true := by
 decide +kernel
def pointBounds55876 : List (Nat × Nat × Nat) := [(7327795200,113036403356433,113036791262255)]
theorem point_links_checked55876 : (cuts55876.take 1).map (fun c => (7327711233-1+2*2^10*c.k,113036261653946+c.lower,113036649559688+c.upper)) = pointBounds55876 := by
 decide +kernel
def cuts55877 : List PrefixCut := [⟨64,227126376,227126501⟩]
theorem checked55877 : checkPrefixCuts (2^48) 7327842305 10 Manual.Count131072.C055877.packed 64 cuts55877 = true := by
 decide +kernel
def cuts55878 : List PrefixCut := [⟨25,85348977,85349026⟩,
⟨64,218979231,218979358⟩]
theorem checked55878 : checkPrefixCuts (2^48) 7327973377 10 Manual.Count131072.C055878.packed 64 cuts55878 = true := by
 decide +kernel
def pointBounds55878 : List (Nat × Nat × Nat) := [(7328024576,113036795843623,113037183749663)]
theorem point_links_checked55878 : (cuts55878.take 1).map (fun c => (7327973377-1+2*2^10*c.k,113036710494646+c.lower,113037098400637+c.upper)) = pointBounds55878 := by
 decide +kernel
def cuts55879 : List PrefixCut := [⟨64,220511720,220511847⟩]
theorem checked55879 : checkPrefixCuts (2^48) 7328104449 10 Manual.Count131072.C055879.packed 64 cuts55879 = true := by
 decide +kernel
def cuts55880 : List PrefixCut := [⟨9,30228350,30228367⟩,
⟨64,221967308,221967435⟩]
theorem checked55880 : checkPrefixCuts (2^48) 7328235521 10 Manual.Count131072.C055880.packed 64 cuts55880 = true := by
 decide +kernel
def pointBounds55880 : List (Nat × Nat × Nat) := [(7328253952,113037180213947,113037568120209)]
theorem point_links_checked55880 : (cuts55880.take 1).map (fun c => (7328235521-1+2*2^10*c.k,113037149985597+c.lower,113037537891842+c.upper)) = pointBounds55880 := by
 decide +kernel
def cuts55881 : List PrefixCut := [⟨57,196460233,196460347⟩,
⟨64,221348813,221348942⟩]
theorem checked55881 : checkPrefixCuts (2^48) 7328366593 10 Manual.Count131072.C055881.packed 64 cuts55881 = true := by
 decide +kernel
def pointBounds55881 : List (Nat × Nat × Nat) := [(7328483328,113037568413138,113037956319624)]
theorem point_links_checked55881 : (cuts55881.take 1).map (fun c => (7328366593-1+2*2^10*c.k,113037371952905+c.lower,113037759859277+c.upper)) = pointBounds55881 := by
 decide +kernel
def cuts55882 : List PrefixCut := [⟨64,226107437,226107567⟩]
theorem checked55882 : checkPrefixCuts (2^48) 7328497665 10 Manual.Count131072.C055882.packed 64 cuts55882 = true := by
 decide +kernel
def cuts55883 : List PrefixCut := [⟨41,142376091,142376170⟩,
⟨64,221379326,221379451⟩]
theorem checked55883 : checkPrefixCuts (2^48) 7328628737 10 Manual.Count131072.C055883.packed 64 cuts55883 = true := by
 decide +kernel
def pointBounds55883 : List (Nat × Nat × Nat) := [(7328712704,113037961785246,113038349691956)]
theorem point_links_checked55883 : (cuts55883.take 1).map (fun c => (7328628737-1+2*2^10*c.k,113037819409155+c.lower,113038207315786+c.upper)) = pointBounds55883 := by
 decide +kernel
def cuts55884 : List PrefixCut := [⟨64,220760850,220760978⟩]
theorem checked55884 : checkPrefixCuts (2^48) 7328759809 10 Manual.Count131072.C055884.packed 64 cuts55884 = true := by
 decide +kernel
def cuts55885 : List PrefixCut := [⟨25,85991203,85991249⟩,
⟨64,221140963,221141085⟩]
theorem checked55885 : checkPrefixCuts (2^48) 7328890881 10 Manual.Count131072.C055885.packed 64 cuts55885 = true := by
 decide +kernel
def pointBounds55885 : List (Nat × Nat × Nat) := [(7328942080,113038347540534,113038735447464)]
theorem point_links_checked55885 : (cuts55885.take 1).map (fun c => (7328890881-1+2*2^10*c.k,113038261549331+c.lower,113038649456215+c.upper)) = pointBounds55885 := by
 decide +kernel
def cuts55886 : List PrefixCut := [⟨64,222788417,222788544⟩]
theorem checked55886 : checkPrefixCuts (2^48) 7329021953 10 Manual.Count131072.C055886.packed 64 cuts55886 = true := by
 decide +kernel
def cuts55887 : List PrefixCut := [⟨9,30992661,30992678⟩,
⟨64,222093148,222093272⟩]
theorem checked55887 : checkPrefixCuts (2^48) 7329153025 10 Manual.Count131072.C055887.packed 64 cuts55887 = true := by
 decide +kernel
def pointBounds55887 : List (Nat × Nat × Nat) := [(7329171456,113038736471372,113039124378522)]
theorem point_links_checked55887 : (cuts55887.take 1).map (fun c => (7329153025-1+2*2^10*c.k,113038705478711+c.lower,113039093385844+c.upper)) = pointBounds55887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000183
