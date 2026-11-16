import PlattAssemblyKernel
import PlattCertificates.Count131072.C055760
import PlattCertificates.Count131072.C055761
import PlattCertificates.Count131072.C055762
import PlattCertificates.Count131072.C055763
import PlattCertificates.Count131072.C055764
import PlattCertificates.Count131072.C055765
import PlattCertificates.Count131072.C055766
import PlattCertificates.Count131072.C055767
import PlattCertificates.Count131072.C055768
import PlattCertificates.Count131072.C055769
import PlattCertificates.Count131072.C055770
import PlattCertificates.Count131072.C055771
import PlattCertificates.Count131072.C055772
import PlattCertificates.Count131072.C055773
import PlattCertificates.Count131072.C055774
import PlattCertificates.Count131072.C055775
import PlattCertificates.Count131072.C055776
import PlattCertificates.Count131072.C055777
import PlattCertificates.Count131072.C055778
import PlattCertificates.Count131072.C055779
import PlattCertificates.Count131072.C055780
import PlattCertificates.Count131072.C055781
import PlattCertificates.Count131072.C055782
import PlattCertificates.Count131072.C055783
import PlattCertificates.Count131072.C055784
import PlattCertificates.Count131072.C055785
import PlattCertificates.Count131072.C055786
import PlattCertificates.Count131072.C055787
import PlattCertificates.Count131072.C055788
import PlattCertificates.Count131072.C055789
import PlattCertificates.Count131072.C055790
import PlattCertificates.Count131072.C055791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55760 : List PrefixCut := [⟨64,224022918,224023045⟩]
theorem checked55760 : checkPrefixCuts (2^48) 7312506881 10 Manual.Count131072.C055760.packed 64 cuts55760 = true := by
 decide +kernel
def cuts55761 : List PrefixCut := [⟨9,30793215,30793233⟩,
⟨64,221670949,221671076⟩]
theorem checked55761 : checkPrefixCuts (2^48) 7312637953 10 Manual.Count131072.C055761.packed 64 cuts55761 = true := by
 decide +kernel
def pointBounds55761 : List (Nat × Nat × Nat) := [(7312656384,113010763050329,113011150941590)]
theorem point_links_checked55761 : (cuts55761.take 1).map (fun c => (7312637953-1+2*2^10*c.k,113010732257114+c.lower,113011120148357+c.upper)) = pointBounds55761 := by
 decide +kernel
def cuts55762 : List PrefixCut := [⟨57,194839274,194839386⟩,
⟨64,220935647,220935773⟩]
theorem checked55762 : checkPrefixCuts (2^48) 7312769025 10 Manual.Count131072.C055762.packed 64 cuts55762 = true := by
 decide +kernel
def pointBounds55762 : List (Nat × Nat × Nat) := [(7312885760,113011148767337,113011536658819)]
theorem point_links_checked55762 : (cuts55762.take 1).map (fun c => (7312769025-1+2*2^10*c.k,113010953928063+c.lower,113011341819433+c.upper)) = pointBounds55762 := by
 decide +kernel
def cuts55763 : List PrefixCut := [⟨64,222009399,222009523⟩]
theorem checked55763 : checkPrefixCuts (2^48) 7312900097 10 Manual.Count131072.C055763.packed 64 cuts55763 = true := by
 decide +kernel
def cuts55764 : List PrefixCut := [⟨41,140254918,140254996⟩,
⟨64,218887808,218887931⟩]
theorem checked55764 : checkPrefixCuts (2^48) 7313031169 10 Manual.Count131072.C055764.packed 64 cuts55764 = true := by
 decide +kernel
def pointBounds55764 : List (Nat × Nat × Nat) := [(7313115136,113011537128027,113011925019725)]
theorem point_links_checked55764 : (cuts55764.take 1).map (fun c => (7313031169-1+2*2^10*c.k,113011396873109+c.lower,113011784764729+c.upper)) = pointBounds55764 := by
 decide +kernel
def cuts55765 : List PrefixCut := [⟨64,220885272,220885398⟩]
theorem checked55765 : checkPrefixCuts (2^48) 7313162241 10 Manual.Count131072.C055765.packed 64 cuts55765 = true := by
 decide +kernel
def cuts55766 : List PrefixCut := [⟨25,85828199,85828248⟩,
⟨64,220265513,220265639⟩]
theorem checked55766 : checkPrefixCuts (2^48) 7313293313 10 Manual.Count131072.C055766.packed 64 cuts55766 = true := by
 decide +kernel
def pointBounds55766 : List (Nat × Nat × Nat) := [(7313344512,113011922474388,113012310366306)]
theorem point_links_checked55766 : (cuts55766.take 1).map (fun c => (7313293313-1+2*2^10*c.k,113011836646189+c.lower,113012224538058+c.upper)) = pointBounds55766 := by
 decide +kernel
def cuts55767 : List PrefixCut := [⟨64,217798391,217798517⟩]
theorem checked55767 : checkPrefixCuts (2^48) 7313424385 10 Manual.Count131072.C055767.packed 64 cuts55767 = true := by
 decide +kernel
def cuts55768 : List PrefixCut := [⟨9,31905465,31905483⟩,
⟨64,225222363,225222489⟩]
theorem checked55768 : checkPrefixCuts (2^48) 7313555457 10 Manual.Count131072.C055768.packed 64 cuts55768 = true := by
 decide +kernel
def pointBounds55768 : List (Nat × Nat × Nat) := [(7313573888,113012306615558,113012694507697)]
theorem point_links_checked55768 : (cuts55768.take 1).map (fun c => (7313555457-1+2*2^10*c.k,113012274710093+c.lower,113012662602214+c.upper)) = pointBounds55768 := by
 decide +kernel
def cuts55769 : List PrefixCut := [⟨57,198470968,198471078⟩,
⟨64,222562827,222562951⟩]
theorem checked55769 : checkPrefixCuts (2^48) 7313686529 10 Manual.Count131072.C055769.packed 64 cuts55769 = true := by
 decide +kernel
def pointBounds55769 : List (Nat × Nat × Nat) := [(7313803264,113012698403424,113013086295781)]
theorem point_links_checked55769 : (cuts55769.take 1).map (fun c => (7313686529-1+2*2^10*c.k,113012499932456+c.lower,113012887824703+c.upper)) = pointBounds55769 := by
 decide +kernel
def cuts55770 : List PrefixCut := [⟨64,222404899,222405023⟩]
theorem checked55770 : checkPrefixCuts (2^48) 7313817601 10 Manual.Count131072.C055770.packed 64 cuts55770 = true := by
 decide +kernel
def cuts55771 : List PrefixCut := [⟨41,139583108,139583188⟩,
⟨64,220322755,220322882⟩]
theorem checked55771 : checkPrefixCuts (2^48) 7313948673 10 Manual.Count131072.C055771.packed 64 cuts55771 = true := by
 decide +kernel
def pointBounds55771 : List (Nat × Nat × Nat) := [(7314032640,113013084483290,113013472375865)]
theorem point_links_checked55771 : (cuts55771.take 1).map (fun c => (7313948673-1+2*2^10*c.k,113012944900182+c.lower,113013332792677+c.upper)) = pointBounds55771 := by
 decide +kernel
def cuts55772 : List PrefixCut := [⟨64,221973625,221973752⟩]
theorem checked55772 : checkPrefixCuts (2^48) 7314079745 10 Manual.Count131072.C055772.packed 64 cuts55772 = true := by
 decide +kernel
def cuts55773 : List PrefixCut := [⟨25,88626709,88626756⟩,
⟨64,225933372,225933498⟩]
theorem checked55773 : checkPrefixCuts (2^48) 7314210817 10 Manual.Count131072.C055773.packed 64 cuts55773 = true := by
 decide +kernel
def pointBounds55773 : List (Nat × Nat × Nat) := [(7314262016,113013475823271,113013863716067)]
theorem point_links_checked55773 : (cuts55773.take 1).map (fun c => (7314210817-1+2*2^10*c.k,113013387196562+c.lower,113013775089311+c.upper)) = pointBounds55773 := by
 decide +kernel
def cuts55774 : List PrefixCut := [⟨64,221272963,221273089⟩]
theorem checked55774 : checkPrefixCuts (2^48) 7314341889 10 Manual.Count131072.C055774.packed 64 cuts55774 = true := by
 decide +kernel
def cuts55775 : List PrefixCut := [⟨9,32440212,32440230⟩,
⟨64,223423987,223424112⟩]
theorem checked55775 : checkPrefixCuts (2^48) 7314472961 10 Manual.Count131072.C055775.packed 64 cuts55775 = true := by
 decide +kernel
def pointBounds55775 : List (Nat × Nat × Nat) := [(7314491392,113013866843109,113014254736128)]
theorem point_links_checked55775 : (cuts55775.take 1).map (fun c => (7314472961-1+2*2^10*c.k,113013834402897+c.lower,113014222295898+c.upper)) = pointBounds55775 := by
 decide +kernel
def cuts55776 : List PrefixCut := [⟨57,197868865,197868975⟩,
⟨64,221534416,221534540⟩]
theorem checked55776 : checkPrefixCuts (2^48) 7314604033 10 Manual.Count131072.C055776.packed 64 cuts55776 = true := by
 decide +kernel
def pointBounds55776 : List (Nat × Nat × Nat) := [(7314720768,113014255695749,113014643588985)]
theorem point_links_checked55776 : (cuts55776.take 1).map (fun c => (7314604033-1+2*2^10*c.k,113014057826884+c.lower,113014445720010+c.upper)) = pointBounds55776 := by
 decide +kernel
def cuts55777 : List PrefixCut := [⟨64,219452511,219452638⟩]
theorem checked55777 : checkPrefixCuts (2^48) 7314735105 10 Manual.Count131072.C055777.packed 64 cuts55777 = true := by
 decide +kernel
def cuts55778 : List PrefixCut := [⟨41,145376002,145376084⟩,
⟨64,224797229,224797357⟩]
theorem checked55778 : checkPrefixCuts (2^48) 7314866177 10 Manual.Count131072.C055778.packed 64 cuts55778 = true := by
 decide +kernel
def pointBounds55778 : List (Nat × Nat × Nat) := [(7314950144,113014644189813,113015032083272)]
theorem point_links_checked55778 : (cuts55778.take 1).map (fun c => (7314866177-1+2*2^10*c.k,113014498813811+c.lower,113014886707188+c.upper)) = pointBounds55778 := by
 decide +kernel
def cuts55779 : List PrefixCut := [⟨64,222792297,222792422⟩]
theorem checked55779 : checkPrefixCuts (2^48) 7314997249 10 Manual.Count131072.C055779.packed 64 cuts55779 = true := by
 decide +kernel
def cuts55780 : List PrefixCut := [⟨25,87230371,87230422⟩,
⟨64,224827636,224827765⟩]
theorem checked55780 : checkPrefixCuts (2^48) 7315128321 10 Manual.Count131072.C055780.packed 64 cuts55780 = true := by
 decide +kernel
def pointBounds55780 : List (Nat × Nat × Nat) := [(7315179520,113015033633708,113015421527389)]
theorem point_links_checked55780 : (cuts55780.take 1).map (fun c => (7315128321-1+2*2^10*c.k,113014946403337+c.lower,113015334296967+c.upper)) = pointBounds55780 := by
 decide +kernel
def cuts55781 : List PrefixCut := [⟨64,220514141,220514269⟩]
theorem checked55781 : checkPrefixCuts (2^48) 7315259393 10 Manual.Count131072.C055781.packed 64 cuts55781 = true := by
 decide +kernel
def cuts55782 : List PrefixCut := [⟨9,31397261,31397279⟩,
⟨64,221356701,221356826⟩]
theorem checked55782 : checkPrefixCuts (2^48) 7315390465 10 Manual.Count131072.C055782.packed 64 cuts55782 = true := by
 decide +kernel
def pointBounds55782 : List (Nat × Nat × Nat) := [(7315408896,113015423142375,113015811036280)]
theorem point_links_checked55782 : (cuts55782.take 1).map (fun c => (7315390465-1+2*2^10*c.k,113015391745114+c.lower,113015779639001+c.upper)) = pointBounds55782 := by
 decide +kernel
def cuts55783 : List PrefixCut := [⟨57,199844799,199844909⟩,
⟨64,222507011,222507135⟩]
theorem checked55783 : checkPrefixCuts (2^48) 7315521537 10 Manual.Count131072.C055783.packed 64 cuts55783 = true := by
 decide +kernel
def pointBounds55783 : List (Nat × Nat × Nat) := [(7315638272,113015812946614,113016200840736)]
theorem point_links_checked55783 : (cuts55783.take 1).map (fun c => (7315521537-1+2*2^10*c.k,113015613101815+c.lower,113016000995827+c.upper)) = pointBounds55783 := by
 decide +kernel
def cuts55784 : List PrefixCut := [⟨64,221618074,221618199⟩]
theorem checked55784 : checkPrefixCuts (2^48) 7315652609 10 Manual.Count131072.C055784.packed 64 cuts55784 = true := by
 decide +kernel
def cuts55785 : List PrefixCut := [⟨41,142933872,142933952⟩,
⟨64,222845313,222845439⟩]
theorem checked55785 : checkPrefixCuts (2^48) 7315783681 10 Manual.Count131072.C055785.packed 64 cuts55785 = true := by
 decide +kernel
def pointBounds55785 : List (Nat × Nat × Nat) := [(7315867648,113016200160772,113016588055113)]
theorem point_links_checked55785 : (cuts55785.take 1).map (fun c => (7315783681-1+2*2^10*c.k,113016057226900+c.lower,113016445121161+c.upper)) = pointBounds55785 := by
 decide +kernel
def cuts55786 : List PrefixCut := [⟨64,221610131,221610259⟩]
theorem checked55786 : checkPrefixCuts (2^48) 7315914753 10 Manual.Count131072.C055786.packed 64 cuts55786 = true := by
 decide +kernel
def cuts55787 : List PrefixCut := [⟨25,86334537,86334587⟩,
⟨64,220990595,220990721⟩]
theorem checked55787 : checkPrefixCuts (2^48) 7316045825 10 Manual.Count131072.C055787.packed 64 cuts55787 = true := by
 decide +kernel
def pointBounds55787 : List (Nat × Nat × Nat) := [(7316097024,113016588016881,113016975911446)]
theorem point_links_checked55787 : (cuts55787.take 1).map (fun c => (7316045825-1+2*2^10*c.k,113016501682344+c.lower,113016889576859+c.upper)) = pointBounds55787 := by
 decide +kernel
def cuts55788 : List PrefixCut := [⟨64,221063580,221063707⟩]
theorem checked55788 : checkPrefixCuts (2^48) 7316176897 10 Manual.Count131072.C055788.packed 64 cuts55788 = true := by
 decide +kernel
def cuts55789 : List PrefixCut := [⟨9,32739851,32739869⟩,
⟨64,224675986,224676116⟩]
theorem checked55789 : checkPrefixCuts (2^48) 7316307969 10 Manual.Count131072.C055789.packed 64 cuts55789 = true := by
 decide +kernel
def pointBounds55789 : List (Nat × Nat × Nat) := [(7316326400,113016976476370,113017364371156)]
theorem point_links_checked55789 : (cuts55789.take 1).map (fun c => (7316307969-1+2*2^10*c.k,113016943736519+c.lower,113017331631287+c.upper)) = pointBounds55789 := by
 decide +kernel
def cuts55790 : List PrefixCut := [⟨57,196164968,196165081⟩,
⟨64,220132350,220132477⟩]
theorem checked55790 : checkPrefixCuts (2^48) 7316439041 10 Manual.Count131072.C055790.packed 64 cuts55790 = true := by
 decide +kernel
def pointBounds55790 : List (Nat × Nat × Nat) := [(7316555776,113017364577473,113017752472484)]
theorem point_links_checked55790 : (cuts55790.take 1).map (fun c => (7316439041-1+2*2^10*c.k,113017168412505+c.lower,113017556307403+c.upper)) = pointBounds55790 := by
 decide +kernel
def cuts55791 : List PrefixCut := [⟨64,222821363,222821488⟩]
theorem checked55791 : checkPrefixCuts (2^48) 7316570113 10 Manual.Count131072.C055791.packed 64 cuts55791 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000180
