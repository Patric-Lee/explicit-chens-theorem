import PlattAssemblyKernel
import PlattCertificates.Count131072.C054896
import PlattCertificates.Count131072.C054897
import PlattCertificates.Count131072.C054898
import PlattCertificates.Count131072.C054899
import PlattCertificates.Count131072.C054900
import PlattCertificates.Count131072.C054901
import PlattCertificates.Count131072.C054902
import PlattCertificates.Count131072.C054903
import PlattCertificates.Count131072.C054904
import PlattCertificates.Count131072.C054905
import PlattCertificates.Count131072.C054906
import PlattCertificates.Count131072.C054907
import PlattCertificates.Count131072.C054908
import PlattCertificates.Count131072.C054909
import PlattCertificates.Count131072.C054910
import PlattCertificates.Count131072.C054911
import PlattCertificates.Count131072.C054912
import PlattCertificates.Count131072.C054913
import PlattCertificates.Count131072.C054914
import PlattCertificates.Count131072.C054915
import PlattCertificates.Count131072.C054916
import PlattCertificates.Count131072.C054917
import PlattCertificates.Count131072.C054918
import PlattCertificates.Count131072.C054919
import PlattCertificates.Count131072.C054920
import PlattCertificates.Count131072.C054921
import PlattCertificates.Count131072.C054922
import PlattCertificates.Count131072.C054923
import PlattCertificates.Count131072.C054924
import PlattCertificates.Count131072.C054925
import PlattCertificates.Count131072.C054926
import PlattCertificates.Count131072.C054927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54896 : List PrefixCut := [⟨64,225670143,225670270⟩]
theorem checked54896 : checkPrefixCuts (2^48) 7199260673 10 Manual.Count131072.C054896.packed 64 cuts54896 = true := by
 decide +kernel
def cuts54897 : List PrefixCut := [⟨15,52663599,52663629⟩,
⟨64,223828509,223828638⟩]
theorem checked54897 : checkPrefixCuts (2^48) 7199391745 10 Manual.Count131072.C054897.packed 64 cuts54897 = true := by
 decide +kernel
def pointBounds54897 : List (Nat × Nat × Nat) := [(7199422464,112817327665547,112817715446977)]
theorem point_links_checked54897 : (cuts54897.take 1).map (fun c => (7199391745-1+2*2^10*c.k,112817275001948+c.lower,112817662783348+c.upper)) = pointBounds54897 := by
 decide +kernel
def cuts54898 : List PrefixCut := [⟨61,216005336,216005460⟩,
⟨64,226561157,226561287⟩]
theorem checked54898 : checkPrefixCuts (2^48) 7199522817 10 Manual.Count131072.C054898.packed 64 cuts54898 = true := by
 decide +kernel
def pointBounds54898 : List (Nat × Nat × Nat) := [(7199647744,112817714835793,112818102617446)]
theorem point_links_checked54898 : (cuts54898.take 1).map (fun c => (7199522817-1+2*2^10*c.k,112817498830457+c.lower,112817886611986+c.upper)) = pointBounds54898 := by
 decide +kernel
def cuts54899 : List PrefixCut := [⟨64,225266885,225267013⟩]
theorem checked54899 : checkPrefixCuts (2^48) 7199653889 10 Manual.Count131072.C054899.packed 64 cuts54899 = true := by
 decide +kernel
def cuts54900 : List PrefixCut := [⟨43,155010340,155010430⟩,
⟨64,227843035,227843166⟩]
theorem checked54900 : checkPrefixCuts (2^48) 7199784961 10 Manual.Count131072.C054900.packed 64 cuts54900 = true := by
 decide +kernel
def pointBounds54900 : List (Nat × Nat × Nat) := [(7199873024,112818105668839,112818493450716)]
theorem point_links_checked54900 : (cuts54900.take 1).map (fun c => (7199784961-1+2*2^10*c.k,112817950658499+c.lower,112818338440286+c.upper)) = pointBounds54900 := by
 decide +kernel
def cuts54901 : List PrefixCut := [⟨64,222443907,222444034⟩]
theorem checked54901 : checkPrefixCuts (2^48) 7199916033 10 Manual.Count131072.C054901.packed 64 cuts54901 = true := by
 decide +kernel
def cuts54902 : List PrefixCut := [⟨25,86357188,86357238⟩,
⟨64,222205327,222205455⟩]
theorem checked54902 : checkPrefixCuts (2^48) 7200047105 10 Manual.Count131072.C054902.packed 64 cuts54902 = true := by
 decide +kernel
def pointBounds54902 : List (Nat × Nat × Nat) := [(7200098304,112818487302629,112818875084724)]
theorem point_links_checked54902 : (cuts54902.take 1).map (fun c => (7200047105-1+2*2^10*c.k,112818400945441+c.lower,112818788727486+c.upper)) = pointBounds54902 := by
 decide +kernel
def cuts54903 : List PrefixCut := [⟨64,226266875,226267004⟩]
theorem checked54903 : checkPrefixCuts (2^48) 7200178177 10 Manual.Count131072.C054903.packed 64 cuts54903 = true := by
 decide +kernel
def cuts54904 : List PrefixCut := [⟨7,24823432,24823446⟩,
⟨64,228021893,228022025⟩]
theorem checked54904 : checkPrefixCuts (2^48) 7200309249 10 Manual.Count131072.C054904.packed 64 cuts54904 = true := by
 decide +kernel
def pointBounds54904 : List (Nat × Nat × Nat) := [(7200323584,112818874241075,112819262023391)]
theorem point_links_checked54904 : (cuts54904.take 1).map (fun c => (7200309249-1+2*2^10*c.k,112818849417643+c.lower,112819237199945+c.upper)) = pointBounds54904 := by
 decide +kernel
def cuts54905 : List PrefixCut := [⟨53,185917052,185917157⟩,
⟨64,226297740,226297867⟩]
theorem checked54905 : checkPrefixCuts (2^48) 7200440321 10 Manual.Count131072.C054905.packed 64 cuts54905 = true := by
 decide +kernel
def pointBounds54905 : List (Nat × Nat × Nat) := [(7200548864,112819263356588,112819651139127)]
theorem point_links_checked54905 : (cuts54905.take 1).map (fun c => (7200440321-1+2*2^10*c.k,112819077439536+c.lower,112819465221970+c.upper)) = pointBounds54905 := by
 decide +kernel
def cuts54906 : List PrefixCut := [⟨64,225629085,225629213⟩]
theorem checked54906 : checkPrefixCuts (2^48) 7200571393 10 Manual.Count131072.C054906.packed 64 cuts54906 = true := by
 decide +kernel
def cuts54907 : List PrefixCut := [⟨35,123562625,123562692⟩,
⟨64,226172223,226172347⟩]
theorem checked54907 : checkPrefixCuts (2^48) 7200702465 10 Manual.Count131072.C054907.packed 64 cuts54907 = true := by
 decide +kernel
def pointBounds54907 : List (Nat × Nat × Nat) := [(7200774144,112819652928986,112820040711742)]
theorem point_links_checked54907 : (cuts54907.take 1).map (fun c => (7200702465-1+2*2^10*c.k,112819529366361+c.lower,112819917149050+c.upper)) = pointBounds54907 := by
 decide +kernel
def cuts54908 : List PrefixCut := [⟨64,226519914,226520042⟩]
theorem checked54908 : checkPrefixCuts (2^48) 7200833537 10 Manual.Count131072.C054908.packed 64 cuts54908 = true := by
 decide +kernel
def cuts54909 : List PrefixCut := [⟨17,59179843,59179877⟩,
⟨64,224717706,224717836⟩]
theorem checked54909 : checkPrefixCuts (2^48) 7200964609 10 Manual.Count131072.C054909.packed 64 cuts54909 = true := by
 decide +kernel
def pointBounds54909 : List (Nat × Nat × Nat) := [(7200999424,112820041238341,112820429021316)]
theorem point_links_checked54909 : (cuts54909.take 1).map (fun c => (7200964609-1+2*2^10*c.k,112819982058498+c.lower,112820369841439+c.upper)) = pointBounds54909 := by
 decide +kernel
def cuts54910 : List PrefixCut := [⟨63,221430337,221430463⟩,
⟨64,225143610,225143738⟩]
theorem checked54910 : checkPrefixCuts (2^48) 7201095681 10 Manual.Count131072.C054910.packed 64 cuts54910 = true := by
 decide +kernel
def pointBounds54910 : List (Nat × Nat × Nat) := [(7201224704,112820428206541,112820815989738)]
theorem point_links_checked54910 : (cuts54910.take 1).map (fun c => (7201095681-1+2*2^10*c.k,112820206776204+c.lower,112820594559275+c.upper)) = pointBounds54910 := by
 decide +kernel
def cuts54911 : List PrefixCut := [⟨64,223732383,223732511⟩]
theorem checked54911 : checkPrefixCuts (2^48) 7201226753 10 Manual.Count131072.C054911.packed 64 cuts54911 = true := by
 decide +kernel
def cuts54912 : List PrefixCut := [⟨45,161699255,161699346⟩,
⟨64,227089728,227089856⟩]
theorem checked54912 : checkPrefixCuts (2^48) 7201357825 10 Manual.Count131072.C054912.packed 64 cuts54912 = true := by
 decide +kernel
def pointBounds54912 : List (Nat × Nat × Nat) := [(7201449984,112820817351452,112821205134870)]
theorem point_links_checked54912 : (cuts54912.take 1).map (fun c => (7201357825-1+2*2^10*c.k,112820655652197+c.lower,112821043435524+c.upper)) = pointBounds54912 := by
 decide +kernel
def cuts54913 : List PrefixCut := [⟨64,224193267,224193396⟩]
theorem checked54913 : checkPrefixCuts (2^48) 7201488897 10 Manual.Count131072.C054913.packed 64 cuts54913 = true := by
 decide +kernel
def cuts54914 : List PrefixCut := [⟨27,95054214,95054269⟩,
⟨64,226651508,226651641⟩]
theorem checked54914 : checkPrefixCuts (2^48) 7201619969 10 Manual.Count131072.C054914.packed 64 cuts54914 = true := by
 decide +kernel
def pointBounds54914 : List (Nat × Nat × Nat) := [(7201675264,112821201989406,112821589773045)]
theorem point_links_checked54914 : (cuts54914.take 1).map (fun c => (7201619969-1+2*2^10*c.k,112821106935192+c.lower,112821494718776+c.upper)) = pointBounds54914 := by
 decide +kernel
def cuts54915 : List PrefixCut := [⟨64,228640674,228640802⟩]
theorem checked54915 : checkPrefixCuts (2^48) 7201751041 10 Manual.Count131072.C054915.packed 64 cuts54915 = true := by
 decide +kernel
def cuts54916 : List PrefixCut := [⟨9,33260033,33260051⟩,
⟨64,228050273,228050401⟩]
theorem checked54916 : checkPrefixCuts (2^48) 7201882113 10 Manual.Count131072.C054916.packed 64 cuts54916 = true := by
 decide +kernel
def pointBounds54916 : List (Nat × Nat × Nat) := [(7201900544,112821595487407,112821983271270)]
theorem point_links_checked54916 : (cuts54916.take 1).map (fun c => (7201882113-1+2*2^10*c.k,112821562227374+c.lower,112821950011219+c.upper)) = pointBounds54916 := by
 decide +kernel
def cuts54917 : List PrefixCut := [⟨55,194240032,194240144⟩,
⟨64,226834543,226834674⟩]
theorem checked54917 : checkPrefixCuts (2^48) 7202013185 10 Manual.Count131072.C054917.packed 64 cuts54917 = true := by
 decide +kernel
def pointBounds54917 : List (Nat × Nat × Nat) := [(7202125824,112821984517679,112822372301764)]
theorem point_links_checked54917 : (cuts54917.take 1).map (fun c => (7202013185-1+2*2^10*c.k,112821790277647+c.lower,112822178061620+c.upper)) = pointBounds54917 := by
 decide +kernel
def cuts54918 : List PrefixCut := [⟨64,222609581,222609708⟩]
theorem checked54918 : checkPrefixCuts (2^48) 7202144257 10 Manual.Count131072.C054918.packed 64 cuts54918 = true := by
 decide +kernel
def cuts54919 : List PrefixCut := [⟨37,133540392,133540468⟩,
⟨64,227842421,227842551⟩]
theorem checked54919 : checkPrefixCuts (2^48) 7202275329 10 Manual.Count131072.C054919.packed 64 cuts54919 = true := by
 decide +kernel
def pointBounds54919 : List (Nat × Nat × Nat) := [(7202351104,112822373262163,112822761046470)]
theorem point_links_checked54919 : (cuts54919.take 1).map (fun c => (7202275329-1+2*2^10*c.k,112822239721771+c.lower,112822627506002+c.upper)) = pointBounds54919 := by
 decide +kernel
def cuts54920 : List PrefixCut := [⟨64,228698007,228698136⟩]
theorem checked54920 : checkPrefixCuts (2^48) 7202406401 10 Manual.Count131072.C054920.packed 64 cuts54920 = true := by
 decide +kernel
def cuts54921 : List PrefixCut := [⟨19,68467909,68467949⟩,
⟨64,228185825,228185958⟩]
theorem checked54921 : checkPrefixCuts (2^48) 7202537473 10 Manual.Count131072.C054921.packed 64 cuts54921 = true := by
 decide +kernel
def pointBounds54921 : List (Nat × Nat × Nat) := [(7202576384,112822764730108,112823152514638)]
theorem point_links_checked54921 : (cuts54921.take 1).map (fun c => (7202537473-1+2*2^10*c.k,112822696262199+c.lower,112823084046689+c.upper)) = pointBounds54921 := by
 decide +kernel
def cuts54922 : List PrefixCut := [⟨64,223765739,223765864⟩]
theorem checked54922 : checkPrefixCuts (2^48) 7202668545 10 Manual.Count131072.C054922.packed 64 cuts54922 = true := by
 decide +kernel
def cuts54923 : List PrefixCut := [⟨1,3829696,3829699⟩,
⟨64,224699555,224699683⟩]
theorem checked54923 : checkPrefixCuts (2^48) 7202799617 10 Manual.Count131072.C054923.packed 64 cuts54923 = true := by
 decide +kernel
def pointBounds54923 : List (Nat × Nat × Nat) := [(7202801664,112823152043459,112823539828210)]
theorem point_links_checked54923 : (cuts54923.take 1).map (fun c => (7202799617-1+2*2^10*c.k,112823148213763+c.lower,112823535998511+c.upper)) = pointBounds54923 := by
 decide +kernel
def cuts54924 : List PrefixCut := [⟨47,164555652,164555748⟩,
⟨64,225633335,225633465⟩]
theorem checked54924 : checkPrefixCuts (2^48) 7202930689 10 Manual.Count131072.C054924.packed 64 cuts54924 = true := by
 decide +kernel
def pointBounds54924 : List (Nat × Nat × Nat) := [(7203026944,112823537468970,112823925253942)]
theorem point_links_checked54924 : (cuts54924.take 1).map (fun c => (7202930689-1+2*2^10*c.k,112823372913318+c.lower,112823760698194+c.upper)) = pointBounds54924 := by
 decide +kernel
def cuts54925 : List PrefixCut := [⟨64,226019993,226020119⟩]
theorem checked54925 : checkPrefixCuts (2^48) 7203061761 10 Manual.Count131072.C054925.packed 64 cuts54925 = true := by
 decide +kernel
def cuts54926 : List PrefixCut := [⟨29,100152421,100152479⟩,
⟨64,223436851,223436980⟩]
theorem checked54926 : checkPrefixCuts (2^48) 7203192833 10 Manual.Count131072.C054926.packed 64 cuts54926 = true := by
 decide +kernel
def pointBounds54926 : List (Nat × Nat × Nat) := [(7203252224,112823924719067,112824312504257)]
theorem point_links_checked54926 : (cuts54926.take 1).map (fun c => (7203192833-1+2*2^10*c.k,112823824566646+c.lower,112824212351778+c.upper)) = pointBounds54926 := by
 decide +kernel
def cuts54927 : List PrefixCut := [⟨64,223393722,223393851⟩]
theorem checked54927 : checkPrefixCuts (2^48) 7203323905 10 Manual.Count131072.C054927.packed 64 cuts54927 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000153
