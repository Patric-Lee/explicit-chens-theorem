import PlattAssemblyKernel
import PlattCertificates.Count131072.C070832
import PlattCertificates.Count131072.C070833
import PlattCertificates.Count131072.C070834
import PlattCertificates.Count131072.C070835
import PlattCertificates.Count131072.C070836
import PlattCertificates.Count131072.C070837
import PlattCertificates.Count131072.C070838
import PlattCertificates.Count131072.C070839
import PlattCertificates.Count131072.C070840
import PlattCertificates.Count131072.C070841
import PlattCertificates.Count131072.C070842
import PlattCertificates.Count131072.C070843
import PlattCertificates.Count131072.C070844
import PlattCertificates.Count131072.C070845
import PlattCertificates.Count131072.C070846
import PlattCertificates.Count131072.C070847
import PlattCertificates.Count131072.C070848
import PlattCertificates.Count131072.C070849
import PlattCertificates.Count131072.C070850
import PlattCertificates.Count131072.C070851
import PlattCertificates.Count131072.C070852
import PlattCertificates.Count131072.C070853
import PlattCertificates.Count131072.C070854
import PlattCertificates.Count131072.C070855
import PlattCertificates.Count131072.C070856
import PlattCertificates.Count131072.C070857
import PlattCertificates.Count131072.C070858
import PlattCertificates.Count131072.C070859
import PlattCertificates.Count131072.C070860
import PlattCertificates.Count131072.C070861
import PlattCertificates.Count131072.C070862
import PlattCertificates.Count131072.C070863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70832 : List PrefixCut := [⟨43,116492415,116492487⟩,
⟨64,173071449,173071553⟩]
theorem checked70832 : checkPrefixCuts (2^48) 9288024065 10 Manual.Count131072.C070832.packed 64 cuts70832 = true := by
 decide +kernel
def pointBounds70832 : List (Nat × Nat × Nat) := [(9288112128,115958764334839,115959153925442)]
theorem point_links_checked70832 : (cuts70832.take 1).map (fun c => (9288024065-1+2*2^10*c.k,115958647842424+c.lower,115959037432955+c.upper)) = pointBounds70832 := by
 decide +kernel
def cuts70833 : List PrefixCut := [⟨64,174281199,174281307⟩]
theorem checked70833 : checkPrefixCuts (2^48) 9288155137 10 Manual.Count131072.C070833.packed 64 cuts70833 = true := by
 decide +kernel
def cuts70834 : List PrefixCut := [⟨57,154490297,154490381⟩,
⟨64,172551412,172551504⟩]
theorem checked70834 : checkPrefixCuts (2^48) 9288286209 10 Manual.Count131072.C070834.packed 64 cuts70834 = true := by
 decide +kernel
def pointBounds70834 : List (Nat × Nat × Nat) := [(9288402944,115959149685369,115959539276196)]
theorem point_links_checked70834 : (cuts70834.take 1).map (fun c => (9288286209-1+2*2^10*c.k,115958995195072+c.lower,115959384785815+c.upper)) = pointBounds70834 := by
 decide +kernel
def cuts70835 : List PrefixCut := [⟨64,175367197,175367299⟩]
theorem checked70835 : checkPrefixCuts (2^48) 9288417281 10 Manual.Count131072.C070835.packed 64 cuts70835 = true := by
 decide +kernel
def cuts70836 : List PrefixCut := [⟨64,171455608,171455713⟩]
theorem checked70836 : checkPrefixCuts (2^48) 9288548353 10 Manual.Count131072.C070836.packed 64 cuts70836 = true := by
 decide +kernel
def cuts70837 : List PrefixCut := [⟨7,19242393,19242405⟩,
⟨64,172968331,172968442⟩]
theorem checked70837 : checkPrefixCuts (2^48) 9288679425 10 Manual.Count131072.C070837.packed 64 cuts70837 = true := by
 decide +kernel
def pointBounds70837 : List (Nat × Nat × Nat) := [(9288693760,115959533811682,115959923402736)]
theorem point_links_checked70837 : (cuts70837.take 1).map (fun c => (9288679425-1+2*2^10*c.k,115959514569289+c.lower,115959904160331+c.upper)) = pointBounds70837 := by
 decide +kernel
def cuts70838 : List PrefixCut := [⟨64,173299209,173299310⟩]
theorem checked70838 : checkPrefixCuts (2^48) 9288810497 10 Manual.Count131072.C070838.packed 64 cuts70838 = true := by
 decide +kernel
def cuts70839 : List PrefixCut := [⟨21,58634525,58634557⟩,
⟨64,174751270,174751374⟩]
theorem checked70839 : checkPrefixCuts (2^48) 9288941569 10 Manual.Count131072.C070839.packed 64 cuts70839 = true := by
 decide +kernel
def pointBounds70839 : List (Nat × Nat × Nat) := [(9288984576,115959919471354,115960309062640)]
theorem point_links_checked70839 : (cuts70839.take 1).map (fun c => (9288941569-1+2*2^10*c.k,115959860836829+c.lower,115960250428083+c.upper)) = pointBounds70839 := by
 decide +kernel
def cuts70840 : List PrefixCut := [⟨64,173991261,173991361⟩]
theorem checked70840 : checkPrefixCuts (2^48) 9289072641 10 Manual.Count131072.C070840.packed 64 cuts70840 = true := by
 decide +kernel
def cuts70841 : List PrefixCut := [⟨35,93812453,93812506⟩,
⟨64,171595023,171595122⟩]
theorem checked70841 : checkPrefixCuts (2^48) 9289203713 10 Manual.Count131072.C070841.packed 64 cuts70841 = true := by
 decide +kernel
def pointBounds70841 : List (Nat × Nat × Nat) := [(9289275392,115960303391813,115960692983324)]
theorem point_links_checked70841 : (cuts70841.take 1).map (fun c => (9289203713-1+2*2^10*c.k,115960209579360+c.lower,115960599170818+c.upper)) = pointBounds70841 := by
 decide +kernel
def cuts70842 : List PrefixCut := [⟨64,173743936,173744042⟩]
theorem checked70842 : checkPrefixCuts (2^48) 9289334785 10 Manual.Count131072.C070842.packed 64 cuts70842 = true := by
 decide +kernel
def cuts70843 : List PrefixCut := [⟨49,133109112,133109190⟩,
⟨64,174408097,174408195⟩]
theorem checked70843 : checkPrefixCuts (2^48) 9289465857 10 Manual.Count131072.C070843.packed 64 cuts70843 = true := by
 decide +kernel
def pointBounds70843 : List (Nat × Nat × Nat) := [(9289566208,115960688027431,115961077619172)]
theorem point_links_checked70843 : (cuts70843.take 1).map (fun c => (9289465857-1+2*2^10*c.k,115960554918319+c.lower,115960944509982+c.upper)) = pointBounds70843 := by
 decide +kernel
def cuts70844 : List PrefixCut := [⟨64,173254234,173254340⟩]
theorem checked70844 : checkPrefixCuts (2^48) 9289596929 10 Manual.Count131072.C070844.packed 64 cuts70844 = true := by
 decide +kernel
def cuts70845 : List PrefixCut := [⟨63,171948944,171949037⟩,
⟨64,175039458,175039553⟩]
theorem checked70845 : checkPrefixCuts (2^48) 9289728001 10 Manual.Count131072.C070845.packed 64 cuts70845 = true := by
 decide +kernel
def pointBounds70845 : List (Nat × Nat × Nat) := [(9289857024,115961074529594,115961464121554)]
theorem point_links_checked70845 : (cuts70845.take 1).map (fun c => (9289728001-1+2*2^10*c.k,115960902580650+c.lower,115961292172517+c.upper)) = pointBounds70845 := by
 decide +kernel
def cuts70846 : List PrefixCut := [⟨64,173885622,173885730⟩]
theorem checked70846 : checkPrefixCuts (2^48) 9289859073 10 Manual.Count131072.C070846.packed 64 cuts70846 = true := by
 decide +kernel
def cuts70847 : List PrefixCut := [⟨64,173065122,173065223⟩]
theorem checked70847 : checkPrefixCuts (2^48) 9289990145 10 Manual.Count131072.C070847.packed 64 cuts70847 = true := by
 decide +kernel
def cuts70848 : List PrefixCut := [⟨13,34721805,34721823⟩,
⟨64,173274765,173274866⟩]
theorem checked70848 : checkPrefixCuts (2^48) 9290121217 10 Manual.Count131072.C070848.packed 64 cuts70848 = true := by
 decide +kernel
def pointBounds70848 : List (Nat × Nat × Nat) := [(9290147840,115961459292657,115961848884846)]
theorem point_links_checked70848 : (cuts70848.take 1).map (fun c => (9290121217-1+2*2^10*c.k,115961424570852+c.lower,115961814163023+c.upper)) = pointBounds70848 := by
 decide +kernel
def cuts70849 : List PrefixCut := [⟨64,172908739,172908843⟩]
theorem checked70849 : checkPrefixCuts (2^48) 9290252289 10 Manual.Count131072.C070849.packed 64 cuts70849 = true := by
 decide +kernel
def cuts70850 : List PrefixCut := [⟨27,71865331,71865376⟩,
⟨64,174027295,174027404⟩]
theorem checked70850 : checkPrefixCuts (2^48) 9290383361 10 Manual.Count131072.C070850.packed 64 cuts70850 = true := by
 decide +kernel
def pointBounds70850 : List (Nat × Nat × Nat) := [(9290438656,115961842619687,115962232212108)]
theorem point_links_checked70850 : (cuts70850.take 1).map (fun c => (9290383361-1+2*2^10*c.k,115961770754356+c.lower,115962160346732+c.upper)) = pointBounds70850 := by
 decide +kernel
def cuts70851 : List PrefixCut := [⟨64,172752390,172752495⟩]
theorem checked70851 : checkPrefixCuts (2^48) 9290514433 10 Manual.Count131072.C070851.packed 64 cuts70851 = true := by
 decide +kernel
def cuts70852 : List PrefixCut := [⟨41,109461084,109461149⟩,
⟨64,172749930,172750036⟩]
theorem checked70852 : checkPrefixCuts (2^48) 9290645505 10 Manual.Count131072.C070852.packed 64 cuts70852 = true := by
 decide +kernel
def pointBounds70852 : List (Nat × Nat × Nat) := [(9290729472,115962226995125,115962616587780)]
theorem point_links_checked70852 : (cuts70852.take 1).map (fun c => (9290645505-1+2*2^10*c.k,115962117534041+c.lower,115962507126631+c.upper)) = pointBounds70852 := by
 decide +kernel
def cuts70853 : List PrefixCut := [⟨64,172686917,172687019⟩]
theorem checked70853 : checkPrefixCuts (2^48) 9290776577 10 Manual.Count131072.C070853.packed 64 cuts70853 = true := by
 decide +kernel
def cuts70854 : List PrefixCut := [⟨55,149508560,149508652⟩,
⟨64,174562805,174562912⟩]
theorem checked70854 : checkPrefixCuts (2^48) 9290907649 10 Manual.Count131072.C070854.packed 64 cuts70854 = true := by
 decide +kernel
def pointBounds70854 : List (Nat × Nat × Nat) := [(9291020288,115962612479448,115963002072338)]
theorem point_links_checked70854 : (cuts70854.take 1).map (fun c => (9290907649-1+2*2^10*c.k,115962462970888+c.lower,115962852563686+c.upper)) = pointBounds70854 := by
 decide +kernel
def cuts70855 : List PrefixCut := [⟨64,174257393,174257498⟩]
theorem checked70855 : checkPrefixCuts (2^48) 9291038721 10 Manual.Count131072.C070855.packed 64 cuts70855 = true := by
 decide +kernel
def cuts70856 : List PrefixCut := [⟨64,173709639,173709741⟩]
theorem checked70856 : checkPrefixCuts (2^48) 9291169793 10 Manual.Count131072.C070856.packed 64 cuts70856 = true := by
 decide +kernel
def cuts70857 : List PrefixCut := [⟨5,13390143,13390149⟩,
⟨64,172434815,172434923⟩]
theorem checked70857 : checkPrefixCuts (2^48) 9291300865 10 Manual.Count131072.C070857.packed 64 cuts70857 = true := by
 decide +kernel
def pointBounds70857 : List (Nat × Nat × Nat) := [(9291311104,115962998890868,115963388483986)]
theorem point_links_checked70857 : (cuts70857.take 1).map (fun c => (9291300865-1+2*2^10*c.k,115962985500725+c.lower,115963375093837+c.upper)) = pointBounds70857 := by
 decide +kernel
def cuts70858 : List PrefixCut := [⟨64,172977680,172977787⟩]
theorem checked70858 : checkPrefixCuts (2^48) 9291431937 10 Manual.Count131072.C070858.packed 64 cuts70858 = true := by
 decide +kernel
def cuts70859 : List PrefixCut := [⟨19,50802264,50802291⟩,
⟨64,174853419,174853526⟩]
theorem checked70859 : checkPrefixCuts (2^48) 9291563009 10 Manual.Count131072.C070859.packed 64 cuts70859 = true := by
 decide +kernel
def pointBounds70859 : List (Nat × Nat × Nat) := [(9291601920,115963381715484,115963771308838)]
theorem point_links_checked70859 : (cuts70859.take 1).map (fun c => (9291563009-1+2*2^10*c.k,115963330913220+c.lower,115963720506547+c.upper)) = pointBounds70859 := by
 decide +kernel
def cuts70860 : List PrefixCut := [⟨64,171609621,171609723⟩]
theorem checked70860 : checkPrefixCuts (2^48) 9291694081 10 Manual.Count131072.C070860.packed 64 cuts70860 = true := by
 decide +kernel
def cuts70861 : List PrefixCut := [⟨33,89514735,89514789⟩,
⟨64,174848487,174848592⟩]
theorem checked70861 : checkPrefixCuts (2^48) 9291825153 10 Manual.Count131072.C070861.packed 64 cuts70861 = true := by
 decide +kernel
def pointBounds70861 : List (Nat × Nat × Nat) := [(9291892736,115963766890995,115964156484585)]
theorem point_links_checked70861 : (cuts70861.take 1).map (fun c => (9291825153-1+2*2^10*c.k,115963677376260+c.lower,115964066969796+c.upper)) = pointBounds70861 := by
 decide +kernel
def cuts70862 : List PrefixCut := [⟨64,172543836,172543940⟩]
theorem checked70862 : checkPrefixCuts (2^48) 9291956225 10 Manual.Count131072.C070862.packed 64 cuts70862 = true := by
 decide +kernel
def cuts70863 : List PrefixCut := [⟨47,124771653,124771725⟩,
⟨64,170451267,170451364⟩]
theorem checked70863 : checkPrefixCuts (2^48) 9292087297 10 Manual.Count131072.C070863.packed 64 cuts70863 = true := by
 decide +kernel
def pointBounds70863 : List (Nat × Nat × Nat) := [(9292183552,115964149540236,115964539134053)]
theorem point_links_checked70863 : (cuts70863.take 1).map (fun c => (9292087297-1+2*2^10*c.k,115964024768583+c.lower,115964414362328+c.upper)) = pointBounds70863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000026
