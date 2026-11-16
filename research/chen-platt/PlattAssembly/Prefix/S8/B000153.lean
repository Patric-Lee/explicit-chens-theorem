import PlattAssemblyKernel
import PlattCertificates.Count131072.C074896
import PlattCertificates.Count131072.C074897
import PlattCertificates.Count131072.C074898
import PlattCertificates.Count131072.C074899
import PlattCertificates.Count131072.C074900
import PlattCertificates.Count131072.C074901
import PlattCertificates.Count131072.C074902
import PlattCertificates.Count131072.C074903
import PlattCertificates.Count131072.C074904
import PlattCertificates.Count131072.C074905
import PlattCertificates.Count131072.C074906
import PlattCertificates.Count131072.C074907
import PlattCertificates.Count131072.C074908
import PlattCertificates.Count131072.C074909
import PlattCertificates.Count131072.C074910
import PlattCertificates.Count131072.C074911
import PlattCertificates.Count131072.C074912
import PlattCertificates.Count131072.C074913
import PlattCertificates.Count131072.C074914
import PlattCertificates.Count131072.C074915
import PlattCertificates.Count131072.C074916
import PlattCertificates.Count131072.C074917
import PlattCertificates.Count131072.C074918
import PlattCertificates.Count131072.C074919
import PlattCertificates.Count131072.C074920
import PlattCertificates.Count131072.C074921
import PlattCertificates.Count131072.C074922
import PlattCertificates.Count131072.C074923
import PlattCertificates.Count131072.C074924
import PlattCertificates.Count131072.C074925
import PlattCertificates.Count131072.C074926
import PlattCertificates.Count131072.C074927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74896 : List PrefixCut := [⟨64,165117143,165117242⟩]
theorem checked74896 : checkPrefixCuts (2^48) 9820700673 10 Manual.Count131072.C074896.packed 64 cuts74896 = true := by
 decide +kernel
def cuts74897 : List PrefixCut := [⟨53,134877939,134878020⟩,
⟨64,162793417,162793512⟩]
theorem checked74897 : checkPrefixCuts (2^48) 9820831745 10 Manual.Count131072.C074897.packed 64 cuts74897 = true := by
 decide +kernel
def pointBounds74897 : List (Nat × Nat × Nat) := [(9820940288,116642053040659,116642443037998)]
theorem point_links_checked74897 : (cuts74897.take 1).map (fun c => (9820831745-1+2*2^10*c.k,116641918162720+c.lower,116642308159978+c.upper)) = pointBounds74897 := by
 decide +kernel
def cuts74898 : List PrefixCut := [⟨64,161816778,161816875⟩]
theorem checked74898 : checkPrefixCuts (2^48) 9820962817 10 Manual.Count131072.C074898.packed 64 cuts74898 = true := by
 decide +kernel
def cuts74899 : List PrefixCut := [⟨64,162932366,162932465⟩]
theorem checked74899 : checkPrefixCuts (2^48) 9821093889 10 Manual.Count131072.C074899.packed 64 cuts74899 = true := by
 decide +kernel
def cuts74900 : List PrefixCut := [⟨11,27656730,27656746⟩,
⟨64,163388739,163388836⟩]
theorem checked74900 : checkPrefixCuts (2^48) 9821224961 10 Manual.Count131072.C074900.packed 64 cuts74900 = true := by
 decide +kernel
def pointBounds74900 : List (Nat × Nat × Nat) := [(9821247488,116642433362011,116642823359576)]
theorem point_links_checked74900 : (cuts74900.take 1).map (fun c => (9821224961-1+2*2^10*c.k,116642405705281+c.lower,116642795702830+c.upper)) = pointBounds74900 := by
 decide +kernel
def cuts74901 : List PrefixCut := [⟨64,163214604,163214702⟩]
theorem checked74901 : checkPrefixCuts (2^48) 9821356033 10 Manual.Count131072.C074901.packed 64 cuts74901 = true := by
 decide +kernel
def cuts74902 : List PrefixCut := [⟨33,83741577,83741625⟩,
⟨64,160088627,160088723⟩]
theorem checked74902 : checkPrefixCuts (2^48) 9821487105 10 Manual.Count131072.C074902.packed 64 cuts74902 = true := by
 decide +kernel
def pointBounds74902 : List (Nat × Nat × Nat) := [(9821554688,116642816050201,116643206047993)]
theorem point_links_checked74902 : (cuts74902.take 1).map (fun c => (9821487105-1+2*2^10*c.k,116642732308624+c.lower,116643122306368+c.upper)) = pointBounds74902 := by
 decide +kernel
def cuts74903 : List PrefixCut := [⟨64,163124275,163124374⟩]
theorem checked74903 : checkPrefixCuts (2^48) 9821618177 10 Manual.Count131072.C074903.packed 64 cuts74903 = true := by
 decide +kernel
def cuts74904 : List PrefixCut := [⟨55,140310358,140310442⟩,
⟨64,164153791,164153887⟩]
theorem checked74904 : checkPrefixCuts (2^48) 9821749249 10 Manual.Count131072.C074904.packed 64 cuts74904 = true := by
 decide +kernel
def pointBounds74904 : List (Nat × Nat × Nat) := [(9821861888,116643195831884,116643585829907)]
theorem point_links_checked74904 : (cuts74904.take 1).map (fun c => (9821749249-1+2*2^10*c.k,116643055521526+c.lower,116643445519465+c.upper)) = pointBounds74904 := by
 decide +kernel
def cuts74905 : List PrefixCut := [⟨64,165211936,165212036⟩]
theorem checked74905 : checkPrefixCuts (2^48) 9821880321 10 Manual.Count131072.C074905.packed 64 cuts74905 = true := by
 decide +kernel
def cuts74906 : List PrefixCut := [⟨64,162258029,162258127⟩]
theorem checked74906 : checkPrefixCuts (2^48) 9822011393 10 Manual.Count131072.C074906.packed 64 cuts74906 = true := by
 decide +kernel
def cuts74907 : List PrefixCut := [⟨13,32726452,32726474⟩,
⟨64,165207531,165207626⟩]
theorem checked74907 : checkPrefixCuts (2^48) 9822142465 10 Manual.Count131072.C074907.packed 64 cuts74907 = true := by
 decide +kernel
def pointBounds74907 : List (Nat × Nat × Nat) := [(9822169088,116643579871734,116643969869989)]
theorem point_links_checked74907 : (cuts74907.take 1).map (fun c => (9822142465-1+2*2^10*c.k,116643547145282+c.lower,116643937143515+c.upper)) = pointBounds74907 := by
 decide +kernel
def cuts74908 : List PrefixCut := [⟨64,164345621,164345726⟩]
theorem checked74908 : checkPrefixCuts (2^48) 9822273537 10 Manual.Count131072.C074908.packed 64 cuts74908 = true := by
 decide +kernel
def cuts74909 : List PrefixCut := [⟨35,88777249,88777303⟩,
⟨64,162308852,162308949⟩]
theorem checked74909 : checkPrefixCuts (2^48) 9822404609 10 Manual.Count131072.C074909.packed 64 cuts74909 = true := by
 decide +kernel
def pointBounds74909 : List (Nat × Nat × Nat) := [(9822476288,116643965475683,116644355474170)]
theorem point_links_checked74909 : (cuts74909.take 1).map (fun c => (9822404609-1+2*2^10*c.k,116643876698434+c.lower,116644266696867+c.upper)) = pointBounds74909 := by
 decide +kernel
def cuts74910 : List PrefixCut := [⟨64,164570485,164570586⟩]
theorem checked74910 : checkPrefixCuts (2^48) 9822535681 10 Manual.Count131072.C074910.packed 64 cuts74910 = true := by
 decide +kernel
def cuts74911 : List PrefixCut := [⟨57,144968056,144968138⟩,
⟨64,161645434,161645526⟩]
theorem checked74911 : checkPrefixCuts (2^48) 9822666753 10 Manual.Count131072.C074911.packed 64 cuts74911 = true := by
 decide +kernel
def pointBounds74911 : List (Nat × Nat × Nat) := [(9822783488,116644348545827,116644738544540)]
theorem point_links_checked74911 : (cuts74911.take 1).map (fun c => (9822666753-1+2*2^10*c.k,116644203577771+c.lower,116644593576402+c.upper)) = pointBounds74911 := by
 decide +kernel
def cuts74912 : List PrefixCut := [⟨64,165798274,165798375⟩]
theorem checked74912 : checkPrefixCuts (2^48) 9822797825 10 Manual.Count131072.C074912.packed 64 cuts74912 = true := by
 decide +kernel
def cuts74913 : List PrefixCut := [⟨64,160007808,160007910⟩]
theorem checked74913 : checkPrefixCuts (2^48) 9822928897 10 Manual.Count131072.C074913.packed 64 cuts74913 = true := by
 decide +kernel
def cuts74914 : List PrefixCut := [⟨15,38884096,38884121⟩,
⟨64,163014378,163014479⟩]
theorem checked74914 : checkPrefixCuts (2^48) 9823059969 10 Manual.Count131072.C074914.packed 64 cuts74914 = true := by
 decide +kernel
def pointBounds74914 : List (Nat × Nat × Nat) := [(9823090688,116644729913383,116645119912334)]
theorem point_links_checked74914 : (cuts74914.take 1).map (fun c => (9823059969-1+2*2^10*c.k,116644691029287+c.lower,116645081028213+c.upper)) = pointBounds74914 := by
 decide +kernel
def cuts74915 : List PrefixCut := [⟨64,163413352,163413450⟩]
theorem checked74915 : checkPrefixCuts (2^48) 9823191041 10 Manual.Count131072.C074915.packed 64 cuts74915 = true := by
 decide +kernel
def cuts74916 : List PrefixCut := [⟨37,96132918,96132975⟩,
⟨64,163525800,163525900⟩]
theorem checked74916 : checkPrefixCuts (2^48) 9823322113 10 Manual.Count131072.C074916.packed 64 cuts74916 = true := by
 decide +kernel
def pointBounds74916 : List (Nat × Nat × Nat) := [(9823397888,116645113589935,116645503589117)]
theorem point_links_checked74916 : (cuts74916.take 1).map (fun c => (9823322113-1+2*2^10*c.k,116645017457017+c.lower,116645407456142+c.upper)) = pointBounds74916 := by
 decide +kernel
def cuts74917 : List PrefixCut := [⟨64,163036505,163036602⟩]
theorem checked74917 : checkPrefixCuts (2^48) 9823453185 10 Manual.Count131072.C074917.packed 64 cuts74917 = true := by
 decide +kernel
def cuts74918 : List PrefixCut := [⟨59,151630607,151630699⟩,
⟨64,164381017,164381117⟩]
theorem checked74918 : checkPrefixCuts (2^48) 9823584257 10 Manual.Count131072.C074918.packed 64 cuts74918 = true := by
 decide +kernel
def pointBounds74918 : List (Nat × Nat × Nat) := [(9823705088,116645495649929,116645885649343)]
theorem point_links_checked74918 : (cuts74918.take 1).map (fun c => (9823584257-1+2*2^10*c.k,116645344019322+c.lower,116645734018644+c.upper)) = pointBounds74918 := by
 decide +kernel
def cuts74919 : List PrefixCut := [⟨64,163318675,163318770⟩]
theorem checked74919 : checkPrefixCuts (2^48) 9823715329 10 Manual.Count131072.C074919.packed 64 cuts74919 = true := by
 decide +kernel
def cuts74920 : List PrefixCut := [⟨64,161769290,161769383⟩]
theorem checked74920 : checkPrefixCuts (2^48) 9823846401 10 Manual.Count131072.C074920.packed 64 cuts74920 = true := by
 decide +kernel
def cuts74921 : List PrefixCut := [⟨17,43063618,43063643⟩,
⟨64,164918801,164918893⟩]
theorem checked74921 : checkPrefixCuts (2^48) 9823977473 10 Manual.Count131072.C074921.packed 64 cuts74921 = true := by
 decide +kernel
def pointBounds74921 : List (Nat × Nat × Nat) := [(9824012288,116645876551922,116646266551557)]
theorem point_links_checked74921 : (cuts74921.take 1).map (fun c => (9823977473-1+2*2^10*c.k,116645833488304+c.lower,116646223487914+c.upper)) = pointBounds74921 := by
 decide +kernel
def cuts74922 : List PrefixCut := [⟨64,162710461,162710561⟩]
theorem checked74922 : checkPrefixCuts (2^48) 9824108545 10 Manual.Count131072.C074922.packed 64 cuts74922 = true := by
 decide +kernel
def cuts74923 : List PrefixCut := [⟨39,98960359,98960421⟩,
⟨64,163395904,163396007⟩]
theorem checked74923 : checkPrefixCuts (2^48) 9824239617 10 Manual.Count131072.C074923.packed 64 cuts74923 = true := by
 decide +kernel
def pointBounds74923 : List (Nat × Nat × Nat) := [(9824319488,116646260077925,116646650077789)]
theorem point_links_checked74923 : (cuts74923.take 1).map (fun c => (9824239617-1+2*2^10*c.k,116646161117566+c.lower,116646551117368+c.upper)) = pointBounds74923 := by
 decide +kernel
def cuts74924 : List PrefixCut := [⟨64,163737536,163737637⟩]
theorem checked74924 : checkPrefixCuts (2^48) 9824370689 10 Manual.Count131072.C074924.packed 64 cuts74924 = true := by
 decide +kernel
def cuts74925 : List PrefixCut := [⟨61,158320531,158320625⟩,
⟨64,165683561,165683660⟩]
theorem checked74925 : checkPrefixCuts (2^48) 9824501761 10 Manual.Count131072.C074925.packed 64 cuts74925 = true := by
 decide +kernel
def pointBounds74925 : List (Nat × Nat × Nat) := [(9824626688,116646646571537,116647036571637)]
theorem point_links_checked74925 : (cuts74925.take 1).map (fun c => (9824501761-1+2*2^10*c.k,116646488251006+c.lower,116646878251012+c.upper)) = pointBounds74925 := by
 decide +kernel
def cuts74926 : List PrefixCut := [⟨64,163389370,163389473⟩]
theorem checked74926 : checkPrefixCuts (2^48) 9824632833 10 Manual.Count131072.C074926.packed 64 cuts74926 = true := by
 decide +kernel
def cuts74927 : List PrefixCut := [⟨64,162355822,162355919⟩]
theorem checked74927 : checkPrefixCuts (2^48) 9824763905 10 Manual.Count131072.C074927.packed 64 cuts74927 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000153
