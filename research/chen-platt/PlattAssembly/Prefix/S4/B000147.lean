import PlattAssemblyKernel
import PlattCertificates.Count131072.C034704
import PlattCertificates.Count131072.C034705
import PlattCertificates.Count131072.C034706
import PlattCertificates.Count131072.C034707
import PlattCertificates.Count131072.C034708
import PlattCertificates.Count131072.C034709
import PlattCertificates.Count131072.C034710
import PlattCertificates.Count131072.C034711
import PlattCertificates.Count131072.C034712
import PlattCertificates.Count131072.C034713
import PlattCertificates.Count131072.C034714
import PlattCertificates.Count131072.C034715
import PlattCertificates.Count131072.C034716
import PlattCertificates.Count131072.C034717
import PlattCertificates.Count131072.C034718
import PlattCertificates.Count131072.C034719
import PlattCertificates.Count131072.C034720
import PlattCertificates.Count131072.C034721
import PlattCertificates.Count131072.C034722
import PlattCertificates.Count131072.C034723
import PlattCertificates.Count131072.C034724
import PlattCertificates.Count131072.C034725
import PlattCertificates.Count131072.C034726
import PlattCertificates.Count131072.C034727
import PlattCertificates.Count131072.C034728
import PlattCertificates.Count131072.C034729
import PlattCertificates.Count131072.C034730
import PlattCertificates.Count131072.C034731
import PlattCertificates.Count131072.C034732
import PlattCertificates.Count131072.C034733
import PlattCertificates.Count131072.C034734
import PlattCertificates.Count131072.C034735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts34704 : List PrefixCut := [⟨64,361989154,361989381⟩]
theorem checked34704 : checkPrefixCuts (2^48) 4552654849 10 Manual.Count131072.C034704.packed 64 cuts34704 = true := by
 decide +kernel
def cuts34705 : List PrefixCut := [⟨1,5997000,5997004⟩,
⟨64,364389840,364390069⟩]
theorem checked34705 : checkPrefixCuts (2^48) 4552785921 10 Manual.Count131072.C034705.packed 64 cuts34705 = true := by
 decide +kernel
def pointBounds34705 : List (Nat × Nat × Nat) := [(4552787968,107076187916156,107076572331869)]
theorem point_links_checked34705 : (cuts34705.take 1).map (fun c => (4552785921-1+2*2^10*c.k,107076181919156+c.lower,107076566334865+c.upper)) = pointBounds34705 := by
 decide +kernel
def cuts34706 : List PrefixCut := [⟨7,40555809,40555835⟩,
⟨64,363019320,363019546⟩]
theorem checked34706 : checkPrefixCuts (2^48) 4552916993 10 Manual.Count131072.C034706.packed 64 cuts34706 = true := by
 decide +kernel
def pointBounds34706 : List (Nat × Nat × Nat) := [(4552931328,107076586864805,107076971280769)]
theorem point_links_checked34706 : (cuts34706.take 1).map (fun c => (4552916993-1+2*2^10*c.k,107076546308996+c.lower,107076930724934+c.upper)) = pointBounds34706 := by
 decide +kernel
def cuts34707 : List PrefixCut := [⟨13,74185228,74185272⟩,
⟨64,364616172,364616396⟩]
theorem checked34707 : checkPrefixCuts (2^48) 4553048065 10 Manual.Count131072.C034707.packed 64 cuts34707 = true := by
 decide +kernel
def pointBounds34707 : List (Nat × Nat × Nat) := [(4553074688,107076983513544,107077367929752)]
theorem point_links_checked34707 : (cuts34707.take 1).map (fun c => (4553048065-1+2*2^10*c.k,107076909328316+c.lower,107077293744480+c.upper)) = pointBounds34707 := by
 decide +kernel
def cuts34708 : List PrefixCut := [⟨19,107318045,107318112⟩,
⟨64,364172943,364173171⟩]
theorem checked34708 : checkPrefixCuts (2^48) 4553179137 10 Manual.Count131072.C034708.packed 64 cuts34708 = true := by
 decide +kernel
def pointBounds34708 : List (Nat × Nat × Nat) := [(4553218048,107077381262533,107077765678988)]
theorem point_links_checked34708 : (cuts34708.take 1).map (fun c => (4553179137-1+2*2^10*c.k,107077273944488+c.lower,107077658360876+c.upper)) = pointBounds34708 := by
 decide +kernel
def cuts34709 : List PrefixCut := [⟨25,144157929,144158018⟩,
⟨64,363791603,363791834⟩]
theorem checked34709 : checkPrefixCuts (2^48) 4553310209 10 Manual.Count131072.C034709.packed 64 cuts34709 = true := by
 decide +kernel
def pointBounds34709 : List (Nat × Nat × Nat) := [(4553361408,107077782275360,107078166692065)]
theorem point_links_checked34709 : (cuts34709.take 1).map (fun c => (4553310209-1+2*2^10*c.k,107077638117431+c.lower,107078022534047+c.upper)) = pointBounds34709 := by
 decide +kernel
def cuts34710 : List PrefixCut := [⟨31,173145026,173145136⟩,
⟨64,357785042,357785270⟩]
theorem checked34710 : checkPrefixCuts (2^48) 4553441281 10 Manual.Count131072.C034710.packed 64 cuts34710 = true := by
 decide +kernel
def pointBounds34710 : List (Nat × Nat × Nat) := [(4553504768,107078175054060,107078559471017)]
theorem point_links_checked34710 : (cuts34710.take 1).map (fun c => (4553441281-1+2*2^10*c.k,107078001909034+c.lower,107078386325881+c.upper)) = pointBounds34710 := by
 decide +kernel
def cuts34711 : List PrefixCut := [⟨37,209857064,209857198⟩,
⟨64,361174510,361174736⟩]
theorem checked34711 : checkPrefixCuts (2^48) 4553572353 10 Manual.Count131072.C034711.packed 64 cuts34711 = true := by
 decide +kernel
def pointBounds34711 : List (Nat × Nat × Nat) := [(4553648128,107078569551140,107078953968349)]
theorem point_links_checked34711 : (cuts34711.take 1).map (fun c => (4553572353-1+2*2^10*c.k,107078359694076+c.lower,107078744111151+c.upper)) = pointBounds34711 := by
 decide +kernel
def cuts34712 : List PrefixCut := [⟨43,245577898,245578052⟩,
⟨64,363945610,363945839⟩]
theorem checked34712 : checkPrefixCuts (2^48) 4553703425 10 Manual.Count131072.C034712.packed 64 cuts34712 = true := by
 decide +kernel
def pointBounds34712 : List (Nat × Nat × Nat) := [(4553791488,107078966446484,107079350863939)]
theorem point_links_checked34712 : (cuts34712.take 1).map (fun c => (4553703425-1+2*2^10*c.k,107078720868586+c.lower,107079105285887+c.upper)) = pointBounds34712 := by
 decide +kernel
def cuts34713 : List PrefixCut := [⟨49,277217119,277217297⟩,
⟨64,364553172,364553404⟩]
theorem checked34713 : checkPrefixCuts (2^48) 4553834497 10 Manual.Count131072.C034713.packed 64 cuts34713 = true := by
 decide +kernel
def pointBounds34713 : List (Nat × Nat × Nat) := [(4553934848,107079362031315,107079746449023)]
theorem point_links_checked34713 : (cuts34713.take 1).map (fun c => (4553834497-1+2*2^10*c.k,107079084814196+c.lower,107079469231726+c.upper)) = pointBounds34713 := by
 decide +kernel
def cuts34714 : List PrefixCut := [⟨55,312624751,312624946⟩,
⟨64,361823193,361823418⟩]
theorem checked34714 : checkPrefixCuts (2^48) 4553965569 10 Manual.Count131072.C034714.packed 64 cuts34714 = true := by
 decide +kernel
def pointBounds34714 : List (Nat × Nat × Nat) := [(4554078208,107079761992119,107080146410076)]
theorem point_links_checked34714 : (cuts34714.take 1).map (fun c => (4553965569-1+2*2^10*c.k,107079449367368+c.lower,107079833785130+c.upper)) = pointBounds34714 := by
 decide +kernel
def cuts34715 : List PrefixCut := [⟨61,346732288,346732509⟩,
⟨64,363172478,363172710⟩]
theorem checked34715 : checkPrefixCuts (2^48) 4554096641 10 Manual.Count131072.C034715.packed 64 cuts34715 = true := by
 decide +kernel
def pointBounds34715 : List (Nat × Nat × Nat) := [(4554221568,107080157922849,107080542341057)]
theorem point_links_checked34715 : (cuts34715.take 1).map (fun c => (4554096641-1+2*2^10*c.k,107079811190561+c.lower,107080195608548+c.upper)) = pointBounds34715 := by
 decide +kernel
def cuts34716 : List PrefixCut := [⟨64,363471088,363471317⟩]
theorem checked34716 : checkPrefixCuts (2^48) 4554227713 10 Manual.Count131072.C034716.packed 64 cuts34716 = true := by
 decide +kernel
def cuts34717 : List PrefixCut := [⟨3,16254285,16254296⟩,
⟨64,367972159,367972389⟩]
theorem checked34717 : checkPrefixCuts (2^48) 4554358785 10 Manual.Count131072.C034717.packed 64 cuts34717 = true := by
 decide +kernel
def pointBounds34717 : List (Nat × Nat × Nat) := [(4554364928,107080554088412,107080938506871)]
theorem point_links_checked34717 : (cuts34717.take 1).map (fun c => (4554358785-1+2*2^10*c.k,107080537834127+c.lower,107080922252575+c.upper)) = pointBounds34717 := by
 decide +kernel
def cuts34718 : List PrefixCut := [⟨9,53149298,53149328⟩,
⟨64,368394225,368394449⟩]
theorem checked34718 : checkPrefixCuts (2^48) 4554489857 10 Manual.Count131072.C034718.packed 64 cuts34718 = true := by
 decide +kernel
def pointBounds34718 : List (Nat × Nat × Nat) := [(4554508288,107080958955584,107081343374292)]
theorem point_links_checked34718 : (cuts34718.take 1).map (fun c => (4554489857-1+2*2^10*c.k,107080905806286+c.lower,107081290224964+c.upper)) = pointBounds34718 := by
 decide +kernel
def cuts34719 : List PrefixCut := [⟨15,84665504,84665561⟩,
⟨64,366097029,366097264⟩]
theorem checked34719 : checkPrefixCuts (2^48) 4554620929 10 Manual.Count131072.C034719.packed 64 cuts34719 = true := by
 decide +kernel
def pointBounds34719 : List (Nat × Nat × Nat) := [(4554651648,107081358866015,107081743284974)]
theorem point_links_checked34719 : (cuts34719.take 1).map (fun c => (4554620929-1+2*2^10*c.k,107081274200511+c.lower,107081658619413+c.upper)) = pointBounds34719 := by
 decide +kernel
def cuts34720 : List PrefixCut := [⟨21,117662969,117663043⟩,
⟨64,358052861,358053084⟩]
theorem checked34720 : checkPrefixCuts (2^48) 4554752001 10 Manual.Count131072.C034720.packed 64 cuts34720 = true := by
 decide +kernel
def pointBounds34720 : List (Nat × Nat × Nat) := [(4554795008,107081757960509,107082142379720)]
theorem point_links_checked34720 : (cuts34720.take 1).map (fun c => (4554752001-1+2*2^10*c.k,107081640297540+c.lower,107082024716677+c.upper)) = pointBounds34720 := by
 decide +kernel
def cuts34721 : List PrefixCut := [⟨27,155169548,155169641⟩,
⟨64,365890600,365890825⟩]
theorem checked34721 : checkPrefixCuts (2^48) 4554883073 10 Manual.Count131072.C034721.packed 64 cuts34721 = true := by
 decide +kernel
def pointBounds34721 : List (Nat × Nat × Nat) := [(4554938368,107082153519949,107082537939402)]
theorem point_links_checked34721 : (cuts34721.take 1).map (fun c => (4554883073-1+2*2^10*c.k,107081998350401+c.lower,107082382769761+c.upper)) = pointBounds34721 := by
 decide +kernel
def cuts34722 : List PrefixCut := [⟨33,186309082,186309194⟩,
⟨64,364149804,364150024⟩]
theorem checked34722 : checkPrefixCuts (2^48) 4555014145 10 Manual.Count131072.C034722.packed 64 cuts34722 = true := by
 decide +kernel
def pointBounds34722 : List (Nat × Nat × Nat) := [(4555081728,107082550550083,107082934969780)]
theorem point_links_checked34722 : (cuts34722.take 1).map (fun c => (4555014145-1+2*2^10*c.k,107082364241001+c.lower,107082748660586+c.upper)) = pointBounds34722 := by
 decide +kernel
def cuts34723 : List PrefixCut := [⟨39,221957567,221957711⟩,
⟨64,365807742,365807975⟩]
theorem checked34723 : checkPrefixCuts (2^48) 4555145217 10 Manual.Count131072.C034723.packed 64 cuts34723 = true := by
 decide +kernel
def pointBounds34723 : List (Nat × Nat × Nat) := [(4555225088,107082950348372,107083334768321)]
theorem point_links_checked34723 : (cuts34723.take 1).map (fun c => (4555145217-1+2*2^10*c.k,107082728390805+c.lower,107083112810610+c.upper)) = pointBounds34723 := by
 decide +kernel
def cuts34724 : List PrefixCut := [⟨45,255564840,255564997⟩,
⟨64,363696372,363696592⟩]
theorem checked34724 : checkPrefixCuts (2^48) 4555276289 10 Manual.Count131072.C034724.packed 64 cuts34724 = true := by
 decide +kernel
def pointBounds34724 : List (Nat × Nat × Nat) := [(4555368448,107083349763387,107083734183582)]
theorem point_links_checked34724 : (cuts34724.take 1).map (fun c => (4555276289-1+2*2^10*c.k,107083094198547+c.lower,107083478618585+c.upper)) = pointBounds34724 := by
 decide +kernel
def cuts34725 : List PrefixCut := [⟨51,288922889,288923074⟩,
⟨64,365663069,365663304⟩]
theorem checked34725 : checkPrefixCuts (2^48) 4555407361 10 Manual.Count131072.C034725.packed 64 cuts34725 = true := by
 decide +kernel
def pointBounds34725 : List (Nat × Nat × Nat) := [(4555511808,107083746817808,107084131238251)]
theorem point_links_checked34725 : (cuts34725.take 1).map (fun c => (4555407361-1+2*2^10*c.k,107083457894919+c.lower,107083842315177+c.upper)) = pointBounds34725 := by
 decide +kernel
def cuts34726 : List PrefixCut := [⟨57,323020403,323020603⟩,
⟨64,362254337,362254564⟩]
theorem checked34726 : checkPrefixCuts (2^48) 4555538433 10 Manual.Count131072.C034726.packed 64 cuts34726 = true := by
 decide +kernel
def pointBounds34726 : List (Nat × Nat × Nat) := [(4555655168,107084146578391,107084530999084)]
theorem point_links_checked34726 : (cuts34726.take 1).map (fun c => (4555538433-1+2*2^10*c.k,107083823557988+c.lower,107084207978481+c.upper)) = pointBounds34726 := by
 decide +kernel
def cuts34727 : List PrefixCut := [⟨63,358228026,358228249⟩,
⟨64,363726790,363727016⟩]
theorem checked34727 : checkPrefixCuts (2^48) 4555669505 10 Manual.Count131072.C034727.packed 64 cuts34727 = true := by
 decide +kernel
def pointBounds34727 : List (Nat × Nat × Nat) := [(4555798528,107084544040351,107084928461294)]
theorem point_links_checked34727 : (cuts34727.take 1).map (fun c => (4555669505-1+2*2^10*c.k,107084185812325+c.lower,107084570233045+c.upper)) = pointBounds34727 := by
 decide +kernel
def cuts34728 : List PrefixCut := [⟨64,369400289,369400520⟩]
theorem checked34728 : checkPrefixCuts (2^48) 4555800577 10 Manual.Count131072.C034728.packed 64 cuts34728 = true := by
 decide +kernel
def cuts34729 : List PrefixCut := [⟨5,28481502,28481519⟩,
⟨64,362470250,362470486⟩]
theorem checked34729 : checkPrefixCuts (2^48) 4555931649 10 Manual.Count131072.C034729.packed 64 cuts34729 = true := by
 decide +kernel
def pointBounds34729 : List (Nat × Nat × Nat) := [(4555941888,107084947420906,107085331842100)]
theorem point_links_checked34729 : (cuts34729.take 1).map (fun c => (4555931649-1+2*2^10*c.k,107084918939404+c.lower,107085303360581+c.upper)) = pointBounds34729 := by
 decide +kernel
def cuts34730 : List PrefixCut := [⟨11,62768622,62768660⟩,
⟨64,367402086,367402315⟩]
theorem checked34730 : checkPrefixCuts (2^48) 4556062721 10 Manual.Count131072.C034730.packed 64 cuts34730 = true := by
 decide +kernel
def pointBounds34730 : List (Nat × Nat × Nat) := [(4556085248,107085344178276,107085728599727)]
theorem point_links_checked34730 : (cuts34730.take 1).map (fun c => (4556062721-1+2*2^10*c.k,107085281409654+c.lower,107085665831067+c.upper)) = pointBounds34730 := by
 decide +kernel
def cuts34731 : List PrefixCut := [⟨17,96621228,96621286⟩,
⟨64,364302669,364302897⟩]
theorem checked34731 : checkPrefixCuts (2^48) 4556193793 10 Manual.Count131072.C034731.packed 64 cuts34731 = true := by
 decide +kernel
def pointBounds34731 : List (Nat × Nat × Nat) := [(4556228608,107085745432968,107086129854668)]
theorem point_links_checked34731 : (cuts34731.take 1).map (fun c => (4556193793-1+2*2^10*c.k,107085648811740+c.lower,107086033233382+c.upper)) = pointBounds34731 := by
 decide +kernel
def cuts34732 : List PrefixCut := [⟨23,130904231,130904311⟩,
⟨64,364786395,364786623⟩]
theorem checked34732 : checkPrefixCuts (2^48) 4556324865 10 Manual.Count131072.C034732.packed 64 cuts34732 = true := by
 decide +kernel
def pointBounds34732 : List (Nat × Nat × Nat) := [(4556371968,107086144018640,107086528440590)]
theorem point_links_checked34732 : (cuts34732.take 1).map (fun c => (4556324865-1+2*2^10*c.k,107086013114409+c.lower,107086397536279+c.upper)) = pointBounds34732 := by
 decide +kernel
def cuts34733 : List PrefixCut := [⟨29,165123399,165123505⟩,
⟨64,365764280,365764508⟩]
theorem checked34733 : checkPrefixCuts (2^48) 4556455937 10 Manual.Count131072.C034733.packed 64 cuts34733 = true := by
 decide +kernel
def pointBounds34733 : List (Nat × Nat × Nat) := [(4556515328,107086543024203,107086927446407)]
theorem point_links_checked34733 : (cuts34733.take 1).map (fun c => (4556455937-1+2*2^10*c.k,107086377900804+c.lower,107086762322902+c.upper)) = pointBounds34733 := by
 decide +kernel
def cuts34734 : List PrefixCut := [⟨35,202367364,202367490⟩,
⟨64,368595292,368595521⟩]
theorem checked34734 : checkPrefixCuts (2^48) 4556587009 10 Manual.Count131072.C034734.packed 64 cuts34734 = true := by
 decide +kernel
def pointBounds34734 : List (Nat × Nat × Nat) := [(4556658688,107086946032448,107087330454900)]
theorem point_links_checked34734 : (cuts34734.take 1).map (fun c => (4556587009-1+2*2^10*c.k,107086743665084+c.lower,107087128087410+c.upper)) = pointBounds34734 := by
 decide +kernel
def cuts34735 : List PrefixCut := [⟨41,231517099,231517245⟩,
⟨64,363087086,363087314⟩]
theorem checked34735 : checkPrefixCuts (2^48) 4556718081 10 Manual.Count131072.C034735.packed 64 cuts34735 = true := by
 decide +kernel
def pointBounds34735 : List (Nat × Nat × Nat) := [(4556802048,107087343777475,107087728200176)]
theorem point_links_checked34735 : (cuts34735.take 1).map (fun c => (4556718081-1+2*2^10*c.k,107087112260376+c.lower,107087496682931+c.upper)) = pointBounds34735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000147
