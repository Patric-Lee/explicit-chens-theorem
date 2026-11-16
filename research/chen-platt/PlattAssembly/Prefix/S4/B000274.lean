import PlattAssemblyKernel
import PlattCertificates.Count131072.C038768
import PlattCertificates.Count131072.C038769
import PlattCertificates.Count131072.C038770
import PlattCertificates.Count131072.C038771
import PlattCertificates.Count131072.C038772
import PlattCertificates.Count131072.C038773
import PlattCertificates.Count131072.C038774
import PlattCertificates.Count131072.C038775
import PlattCertificates.Count131072.C038776
import PlattCertificates.Count131072.C038777
import PlattCertificates.Count131072.C038778
import PlattCertificates.Count131072.C038779
import PlattCertificates.Count131072.C038780
import PlattCertificates.Count131072.C038781
import PlattCertificates.Count131072.C038782
import PlattCertificates.Count131072.C038783
import PlattCertificates.Count131072.C038784
import PlattCertificates.Count131072.C038785
import PlattCertificates.Count131072.C038786
import PlattCertificates.Count131072.C038787
import PlattCertificates.Count131072.C038788
import PlattCertificates.Count131072.C038789
import PlattCertificates.Count131072.C038790
import PlattCertificates.Count131072.C038791
import PlattCertificates.Count131072.C038792
import PlattCertificates.Count131072.C038793
import PlattCertificates.Count131072.C038794
import PlattCertificates.Count131072.C038795
import PlattCertificates.Count131072.C038796
import PlattCertificates.Count131072.C038797
import PlattCertificates.Count131072.C038798
import PlattCertificates.Count131072.C038799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000274
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38768 : List PrefixCut := [⟨64,320253025,320253215⟩]
theorem checked38768 : checkPrefixCuts (2^48) 5085331457 10 Manual.Count131072.C038768.packed 64 cuts38768 = true := by
 decide +kernel
def cuts38769 : List PrefixCut := [⟨5,25073038,25073054⟩,
⟨64,325004700,325004896⟩]
theorem checked38769 : checkPrefixCuts (2^48) 5085462529 10 Manual.Count131072.C038769.packed 64 cuts38769 = true := by
 decide +kernel
def pointBounds38769 : List (Nat × Nat × Nat) := [(5085472768,108473140918959,108473526190018)]
theorem point_links_checked38769 : (cuts38769.take 1).map (fun c => (5085462529-1+2*2^10*c.k,108473115845921+c.lower,108473501116964+c.upper)) = pointBounds38769 := by
 decide +kernel
def cuts38770 : List PrefixCut := [⟨19,96802409,96802466⟩,
⟨64,325494459,325494651⟩]
theorem checked38770 : checkPrefixCuts (2^48) 5085593601 10 Manual.Count131072.C038770.packed 64 cuts38770 = true := by
 decide +kernel
def pointBounds38770 : List (Nat × Nat × Nat) := [(5085632512,108473537653030,108473922924326)]
theorem point_links_checked38770 : (cuts38770.take 1).map (fun c => (5085593601-1+2*2^10*c.k,108473440850621+c.lower,108473826121860+c.upper)) = pointBounds38770 := by
 decide +kernel
def cuts38771 : List PrefixCut := [⟨33,167586804,167586903⟩,
⟨64,322552789,322552983⟩]
theorem checked38771 : checkPrefixCuts (2^48) 5085724673 10 Manual.Count131072.C038771.packed 64 cuts38771 = true := by
 decide +kernel
def pointBounds38771 : List (Nat × Nat × Nat) := [(5085792256,108473933931884,108474319203414)]
theorem point_links_checked38771 : (cuts38771.take 1).map (fun c => (5085724673-1+2*2^10*c.k,108473766345080+c.lower,108474151616511+c.upper)) = pointBounds38771 := by
 decide +kernel
def cuts38772 : List PrefixCut := [⟨47,237204916,237205060⟩,
⟨64,324813536,324813732⟩]
theorem checked38772 : checkPrefixCuts (2^48) 5085855745 10 Manual.Count131072.C038772.packed 64 cuts38772 = true := by
 decide +kernel
def pointBounds38772 : List (Nat × Nat × Nat) := [(5085952000,108474326102785,108474711374554)]
theorem point_links_checked38772 : (cuts38772.take 1).map (fun c => (5085855745-1+2*2^10*c.k,108474088897869+c.lower,108474474169494+c.upper)) = pointBounds38772 := by
 decide +kernel
def cuts38773 : List PrefixCut := [⟨61,308036607,308036794⟩,
⟨64,323753686,323753882⟩]
theorem checked38773 : checkPrefixCuts (2^48) 5085986817 10 Manual.Count131072.C038773.packed 64 cuts38773 = true := by
 decide +kernel
def pointBounds38773 : List (Nat × Nat × Nat) := [(5086111744,108474721748012,108475107020020)]
theorem point_links_checked38773 : (cuts38773.take 1).map (fun c => (5085986817-1+2*2^10*c.k,108474413711405+c.lower,108474798983226+c.upper)) = pointBounds38773 := by
 decide +kernel
def cuts38774 : List PrefixCut := [⟨64,324022013,324022208⟩]
theorem checked38774 : checkPrefixCuts (2^48) 5086117889 10 Manual.Count131072.C038774.packed 64 cuts38774 = true := by
 decide +kernel
def cuts38775 : List PrefixCut := [⟨11,56889773,56889807⟩,
⟨64,326503984,326504176⟩]
theorem checked38775 : checkPrefixCuts (2^48) 5086248961 10 Manual.Count131072.C038775.packed 64 cuts38775 = true := by
 decide +kernel
def pointBounds38775 : List (Nat × Nat × Nat) := [(5086271488,108475118376877,108475503649123)]
theorem point_links_checked38775 : (cuts38775.take 1).map (fun c => (5086248961-1+2*2^10*c.k,108475061487104+c.lower,108475446759316+c.upper)) = pointBounds38775 := by
 decide +kernel
def cuts38776 : List PrefixCut := [⟨25,125563425,125563502⟩,
⟨64,326661540,326661739⟩]
theorem checked38776 : checkPrefixCuts (2^48) 5086380033 10 Manual.Count131072.C038776.packed 64 cuts38776 = true := by
 decide +kernel
def pointBounds38776 : List (Nat × Nat × Nat) := [(5086431232,108475513554513,108475898826994)]
theorem point_links_checked38776 : (cuts38776.take 1).map (fun c => (5086380033-1+2*2^10*c.k,108475387991088+c.lower,108475773263492+c.upper)) = pointBounds38776 := by
 decide +kernel
def cuts38777 : List PrefixCut := [⟨39,197055334,197055449⟩,
⟨64,325048354,325048547⟩]
theorem checked38777 : checkPrefixCuts (2^48) 5086511105 10 Manual.Count131072.C038777.packed 64 cuts38777 = true := by
 decide +kernel
def pointBounds38777 : List (Nat × Nat × Nat) := [(5086590976,108475911707962,108476296980680)]
theorem point_links_checked38777 : (cuts38777.take 1).map (fun c => (5086511105-1+2*2^10*c.k,108475714652628+c.lower,108476099925231+c.upper)) = pointBounds38777 := by
 decide +kernel
def cuts38778 : List PrefixCut := [⟨53,271088633,271088792⟩,
⟨64,327474785,327474978⟩]
theorem checked38778 : checkPrefixCuts (2^48) 5086642177 10 Manual.Count131072.C038778.packed 64 cuts38778 = true := by
 decide +kernel
def pointBounds38778 : List (Nat × Nat × Nat) := [(5086750720,108476310789615,108476696062570)]
theorem point_links_checked38778 : (cuts38778.take 1).map (fun c => (5086642177-1+2*2^10*c.k,108476039700982+c.lower,108476424973778+c.upper)) = pointBounds38778 := by
 decide +kernel
def cuts38779 : List PrefixCut := [⟨64,321932918,321933113⟩]
theorem checked38779 : checkPrefixCuts (2^48) 5086773249 10 Manual.Count131072.C038779.packed 64 cuts38779 = true := by
 decide +kernel
def cuts38780 : List PrefixCut := [⟨3,14773965,14773974⟩,
⟨64,316557360,316557551⟩]
theorem checked38780 : checkPrefixCuts (2^48) 5086904321 10 Manual.Count131072.C038780.packed 64 cuts38780 = true := by
 decide +kernel
def pointBounds38780 : List (Nat × Nat × Nat) := [(5086910464,108476703882650,108477089155843)]
theorem point_links_checked38780 : (cuts38780.take 1).map (fun c => (5086904321-1+2*2^10*c.k,108476689108685+c.lower,108477074381869+c.upper)) = pointBounds38780 := by
 decide +kernel
def cuts38781 : List PrefixCut := [⟨17,84436057,84436108⟩,
⟨64,322856964,322857158⟩]
theorem checked38781 : checkPrefixCuts (2^48) 5087035393 10 Manual.Count131072.C038781.packed 64 cuts38781 = true := by
 decide +kernel
def pointBounds38781 : List (Nat × Nat × Nat) := [(5087070208,108477090102102,108477475375528)]
theorem point_links_checked38781 : (cuts38781.take 1).map (fun c => (5087035393-1+2*2^10*c.k,108477005666045+c.lower,108477390939420+c.upper)) = pointBounds38781 := by
 decide +kernel
def cuts38782 : List PrefixCut := [⟨31,160180466,160180562⟩,
⟨64,328824261,328824456⟩]
theorem checked38782 : checkPrefixCuts (2^48) 5087166465 10 Manual.Count131072.C038782.packed 64 cuts38782 = true := by
 decide +kernel
def pointBounds38782 : List (Nat × Nat × Nat) := [(5087229952,108477488703475,108477873977140)]
theorem point_links_checked38782 : (cuts38782.take 1).map (fun c => (5087166465-1+2*2^10*c.k,108477328523009+c.lower,108477713796578+c.upper)) = pointBounds38782 := by
 decide +kernel
def cuts38783 : List PrefixCut := [⟨45,228119246,228119379⟩,
⟨64,326934603,326934794⟩]
theorem checked38783 : checkPrefixCuts (2^48) 5087297537 10 Manual.Count131072.C038783.packed 64 cuts38783 = true := by
 decide +kernel
def pointBounds38783 : List (Nat × Nat × Nat) := [(5087389696,108477885466516,108478270740413)]
theorem point_links_checked38783 : (cuts38783.take 1).map (fun c => (5087297537-1+2*2^10*c.k,108477657347270+c.lower,108478042621034+c.upper)) = pointBounds38783 := by
 decide +kernel
def cuts38784 : List PrefixCut := [⟨59,301476152,301476332⟩,
⟨64,325985644,325985840⟩]
theorem checked38784 : checkPrefixCuts (2^48) 5087428609 10 Manual.Count131072.C038784.packed 64 cuts38784 = true := by
 decide +kernel
def pointBounds38784 : List (Nat × Nat × Nat) := [(5087549440,108478285758025,108478671032160)]
theorem point_links_checked38784 : (cuts38784.take 1).map (fun c => (5087428609-1+2*2^10*c.k,108477984281873+c.lower,108478369555828+c.upper)) = pointBounds38784 := by
 decide +kernel
def cuts38785 : List PrefixCut := [⟨64,328522202,328522397⟩]
theorem checked38785 : checkPrefixCuts (2^48) 5087559681 10 Manual.Count131072.C038785.packed 64 cuts38785 = true := by
 decide +kernel
def cuts38786 : List PrefixCut := [⟨9,46583304,46583331⟩,
⟨64,325526293,325526489⟩]
theorem checked38786 : checkPrefixCuts (2^48) 5087690753 10 Manual.Count131072.C038786.packed 64 cuts38786 = true := by
 decide +kernel
def pointBounds38786 : List (Nat × Nat × Nat) := [(5087709184,108478685373023,108479070647396)]
theorem point_links_checked38786 : (cuts38786.take 1).map (fun c => (5087690753-1+2*2^10*c.k,108478638789719+c.lower,108479024064065+c.upper)) = pointBounds38786 := by
 decide +kernel
def cuts38787 : List PrefixCut := [⟨23,115182492,115182563⟩,
⟨64,327398814,327399011⟩]
theorem checked38787 : checkPrefixCuts (2^48) 5087821825 10 Manual.Count131072.C038787.packed 64 cuts38787 = true := by
 decide +kernel
def pointBounds38787 : List (Nat × Nat × Nat) := [(5087868928,108479079498504,108479464773117)]
theorem point_links_checked38787 : (cuts38787.take 1).map (fun c => (5087821825-1+2*2^10*c.k,108478964316012+c.lower,108479349590554+c.upper)) = pointBounds38787 := by
 decide +kernel
def cuts38788 : List PrefixCut := [⟨37,190361018,190361136⟩,
⟨64,323020087,323020283⟩]
theorem checked38788 : checkPrefixCuts (2^48) 5087952897 10 Manual.Count131072.C038788.packed 64 cuts38788 = true := by
 decide +kernel
def pointBounds38788 : List (Nat × Nat × Nat) := [(5088028672,108479482075844,108479867350701)]
theorem point_links_checked38788 : (cuts38788.take 1).map (fun c => (5087952897-1+2*2^10*c.k,108479291714826+c.lower,108479676989565+c.upper)) = pointBounds38788 := by
 decide +kernel
def cuts38789 : List PrefixCut := [⟨51,257403194,257403354⟩,
⟨64,323122322,323122520⟩]
theorem checked38789 : checkPrefixCuts (2^48) 5088083969 10 Manual.Count131072.C038789.packed 64 cuts38789 = true := by
 decide +kernel
def pointBounds38789 : List (Nat × Nat × Nat) := [(5088188416,108479872138107,108480257413202)]
theorem point_links_checked38789 : (cuts38789.take 1).map (fun c => (5088083969-1+2*2^10*c.k,108479614734913+c.lower,108480000009848+c.upper)) = pointBounds38789 := by
 decide +kernel
def cuts38790 : List PrefixCut := [⟨64,324220389,324220582⟩]
theorem checked38790 : checkPrefixCuts (2^48) 5088215041 10 Manual.Count131072.C038790.packed 64 cuts38790 = true := by
 decide +kernel
def cuts38791 : List PrefixCut := [⟨1,5144532,5144535⟩,
⟨64,324875850,324876047⟩]
theorem checked38791 : checkPrefixCuts (2^48) 5088346113 10 Manual.Count131072.C038791.packed 64 cuts38791 = true := by
 decide +kernel
def pointBounds38791 : List (Nat × Nat × Nat) := [(5088348160,108480267222156,108480652497485)]
theorem point_links_checked38791 : (cuts38791.take 1).map (fun c => (5088346113-1+2*2^10*c.k,108480262077624+c.lower,108480647352950+c.upper)) = pointBounds38791 := by
 decide +kernel
def cuts38792 : List PrefixCut := [⟨15,74621236,74621283⟩,
⟨64,322876104,322876301⟩]
theorem checked38792 : checkPrefixCuts (2^48) 5088477185 10 Manual.Count131072.C038792.packed 64 cuts38792 = true := by
 decide +kernel
def pointBounds38792 : List (Nat × Nat × Nat) := [(5088507904,108480661574710,108481046850280)]
theorem point_links_checked38792 : (cuts38792.take 1).map (fun c => (5088477185-1+2*2^10*c.k,108480586953474+c.lower,108480972228997+c.upper)) = pointBounds38792 := by
 decide +kernel
def cuts38793 : List PrefixCut := [⟨29,150123263,150123353⟩,
⟨64,326020737,326020933⟩]
theorem checked38793 : checkPrefixCuts (2^48) 5088608257 10 Manual.Count131072.C038793.packed 64 cuts38793 = true := by
 decide +kernel
def pointBounds38793 : List (Nat × Nat × Nat) := [(5088667648,108481059952841,108481445228651)]
theorem point_links_checked38793 : (cuts38793.take 1).map (fun c => (5088608257-1+2*2^10*c.k,108480909829578+c.lower,108481295105298+c.upper)) = pointBounds38793 := by
 decide +kernel
def cuts38794 : List PrefixCut := [⟨43,214613702,214613830⟩,
⟨64,320370428,320370621⟩]
theorem checked38794 : checkPrefixCuts (2^48) 5088739329 10 Manual.Count131072.C038794.packed 64 cuts38794 = true := by
 decide +kernel
def pointBounds38794 : List (Nat × Nat × Nat) := [(5088827392,108481450464017,108481835740061)]
theorem point_links_checked38794 : (cuts38794.take 1).map (fun c => (5088739329-1+2*2^10*c.k,108481235850315+c.lower,108481621126231+c.upper)) = pointBounds38794 := by
 decide +kernel
def cuts38795 : List PrefixCut := [⟨57,286069684,286069858⟩,
⟨64,320638756,320638951⟩]
theorem checked38795 : checkPrefixCuts (2^48) 5088870401 10 Manual.Count131072.C038795.packed 64 cuts38795 = true := by
 decide +kernel
def pointBounds38795 : List (Nat × Nat × Nat) := [(5088987136,108481842290427,108482227566710)]
theorem point_links_checked38795 : (cuts38795.take 1).map (fun c => (5088870401-1+2*2^10*c.k,108481556220743+c.lower,108481941496852+c.upper)) = pointBounds38795 := by
 decide +kernel
def cuts38796 : List PrefixCut := [⟨64,328871629,328871823⟩]
theorem checked38796 : checkPrefixCuts (2^48) 5089001473 10 Manual.Count131072.C038796.packed 64 cuts38796 = true := by
 decide +kernel
def cuts38797 : List PrefixCut := [⟨7,35065864,35065884⟩,
⟨64,321838973,321839163⟩]
theorem checked38797 : checkPrefixCuts (2^48) 5089132545 10 Manual.Count131072.C038797.packed 64 cuts38797 = true := by
 decide +kernel
def pointBounds38797 : List (Nat × Nat × Nat) := [(5089146880,108482240796992,108482626073510)]
theorem point_links_checked38797 : (cuts38797.take 1).map (fun c => (5089132545-1+2*2^10*c.k,108482205731128+c.lower,108482591007626+c.upper)) = pointBounds38797 := by
 decide +kernel
def cuts38798 : List PrefixCut := [⟨21,105968896,105968958⟩,
⟨64,325093804,325093994⟩]
theorem checked38798 : checkPrefixCuts (2^48) 5089263617 10 Manual.Count131072.C038798.packed 64 cuts38798 = true := by
 decide +kernel
def pointBounds38798 : List (Nat × Nat × Nat) := [(5089306624,108482633538997,108483018815747)]
theorem point_links_checked38798 : (cuts38798.take 1).map (fun c => (5089263617-1+2*2^10*c.k,108482527570101+c.lower,108482912846789+c.upper)) = pointBounds38798 := by
 decide +kernel
def cuts38799 : List PrefixCut := [⟨35,174600343,174600446⟩,
⟨64,323592180,323592372⟩]
theorem checked38799 : checkPrefixCuts (2^48) 5089394689 10 Manual.Count131072.C038799.packed 64 cuts38799 = true := by
 decide +kernel
def pointBounds38799 : List (Nat × Nat × Nat) := [(5089466368,108483027264248,108483412541229)]
theorem point_links_checked38799 : (cuts38799.take 1).map (fun c => (5089394689-1+2*2^10*c.k,108482852663905+c.lower,108483237940783+c.upper)) = pointBounds38799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000274
