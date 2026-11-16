import PlattAssemblyKernel
import PlattCertificates.Count131072.C045856
import PlattCertificates.Count131072.C045857
import PlattCertificates.Count131072.C045858
import PlattCertificates.Count131072.C045859
import PlattCertificates.Count131072.C045860
import PlattCertificates.Count131072.C045861
import PlattCertificates.Count131072.C045862
import PlattCertificates.Count131072.C045863
import PlattCertificates.Count131072.C045864
import PlattCertificates.Count131072.C045865
import PlattCertificates.Count131072.C045866
import PlattCertificates.Count131072.C045867
import PlattCertificates.Count131072.C045868
import PlattCertificates.Count131072.C045869
import PlattCertificates.Count131072.C045870
import PlattCertificates.Count131072.C045871
import PlattCertificates.Count131072.C045872
import PlattCertificates.Count131072.C045873
import PlattCertificates.Count131072.C045874
import PlattCertificates.Count131072.C045875
import PlattCertificates.Count131072.C045876
import PlattCertificates.Count131072.C045877
import PlattCertificates.Count131072.C045878
import PlattCertificates.Count131072.C045879
import PlattCertificates.Count131072.C045880
import PlattCertificates.Count131072.C045881
import PlattCertificates.Count131072.C045882
import PlattCertificates.Count131072.C045883
import PlattCertificates.Count131072.C045884
import PlattCertificates.Count131072.C045885
import PlattCertificates.Count131072.C045886
import PlattCertificates.Count131072.C045887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45856 : List PrefixCut := [⟨64,266852987,266853141⟩]
theorem checked45856 : checkPrefixCuts (2^48) 6014369793 10 Manual.Count131072.C045856.packed 64 cuts45856 = true := by
 decide +kernel
def cuts45857 : List PrefixCut := [⟨14,59388266,59388303⟩,
⟨64,274802933,274803097⟩]
theorem checked45857 : checkPrefixCuts (2^48) 6014500865 10 Manual.Count131072.C045857.packed 64 cuts45857 = true := by
 decide +kernel
def pointBounds45857 : List (Nat × Nat × Nat) := [(6014529536,110578450149091,110578836654278)]
theorem point_links_checked45857 : (cuts45857.take 1).map (fun c => (6014500865-1+2*2^10*c.k,110578390760825+c.lower,110578777265975+c.upper)) = pointBounds45857 := by
 decide +kernel
def cuts45858 : List PrefixCut := [⟨42,177785680,177785782⟩,
⟨64,270351159,270351314⟩]
theorem checked45858 : checkPrefixCuts (2^48) 6014631937 10 Manual.Count131072.C045858.packed 64 cuts45858 = true := by
 decide +kernel
def pointBounds45858 : List (Nat × Nat × Nat) := [(6014717952,110578843349438,110579229854854)]
theorem point_links_checked45858 : (cuts45858.take 1).map (fun c => (6014631937-1+2*2^10*c.k,110578665563758+c.lower,110579052069072+c.upper)) = pointBounds45858 := by
 decide +kernel
def cuts45859 : List PrefixCut := [⟨64,273527490,273527649⟩]
theorem checked45859 : checkPrefixCuts (2^48) 6014763009 10 Manual.Count131072.C045859.packed 64 cuts45859 = true := by
 decide +kernel
def cuts45860 : List PrefixCut := [⟨6,25410374,25410389⟩,
⟨64,274504214,274504371⟩]
theorem checked45860 : checkPrefixCuts (2^48) 6014894081 10 Manual.Count131072.C045860.packed 64 cuts45860 = true := by
 decide +kernel
def pointBounds45860 : List (Nat × Nat × Nat) := [(6014906368,110579234852781,110579621358424)]
theorem point_links_checked45860 : (cuts45860.take 1).map (fun c => (6014894081-1+2*2^10*c.k,110579209442407+c.lower,110579595948035+c.upper)) = pointBounds45860 := by
 decide +kernel
def cuts45861 : List PrefixCut := [⟨34,145158169,145158250⟩,
⟨64,272064896,272065051⟩]
theorem checked45861 : checkPrefixCuts (2^48) 6015025153 10 Manual.Count131072.C045861.packed 64 cuts45861 = true := by
 decide +kernel
def pointBounds45861 : List (Nat × Nat × Nat) := [(6015094784,110579629104790,110580015610656)]
theorem point_links_checked45861 : (cuts45861.take 1).map (fun c => (6015025153-1+2*2^10*c.k,110579483946621+c.lower,110579870452406+c.upper)) = pointBounds45861 := by
 decide +kernel
def cuts45862 : List PrefixCut := [⟨62,266537412,266537562⟩,
⟨64,276176827,276176982⟩]
theorem checked45862 : checkPrefixCuts (2^48) 6015156225 10 Manual.Count131072.C045862.packed 64 cuts45862 = true := by
 decide +kernel
def pointBounds45862 : List (Nat × Nat × Nat) := [(6015283200,110580022548929,110580409055019)]
theorem point_links_checked45862 : (cuts45862.take 1).map (fun c => (6015156225-1+2*2^10*c.k,110579756011517+c.lower,110580142517457+c.upper)) = pointBounds45862 := by
 decide +kernel
def cuts45863 : List PrefixCut := [⟨64,268309616,268309777⟩]
theorem checked45863 : checkPrefixCuts (2^48) 6015287297 10 Manual.Count131072.C045863.packed 64 cuts45863 = true := by
 decide +kernel
def cuts45864 : List PrefixCut := [⟨26,111271448,111271513⟩,
⟨64,273216906,273217065⟩]
theorem checked45864 : checkPrefixCuts (2^48) 6015418369 10 Manual.Count131072.C045864.packed 64 cuts45864 = true := by
 decide +kernel
def pointBounds45864 : List (Nat × Nat × Nat) := [(6015471616,110580411769408,110580798275729)]
theorem point_links_checked45864 : (cuts45864.take 1).map (fun c => (6015418369-1+2*2^10*c.k,110580300497960+c.lower,110580687004216+c.upper)) = pointBounds45864 := by
 decide +kernel
def cuts45865 : List PrefixCut := [⟨54,226420641,226420774⟩,
⟨64,267221764,267221922⟩]
theorem checked45865 : checkPrefixCuts (2^48) 6015549441 10 Manual.Count131072.C045865.packed 64 cuts45865 = true := by
 decide +kernel
def pointBounds45865 : List (Nat × Nat × Nat) := [(6015660032,110580800135507,110581186642055)]
theorem point_links_checked45865 : (cuts45865.take 1).map (fun c => (6015549441-1+2*2^10*c.k,110580573714866+c.lower,110580960221281+c.upper)) = pointBounds45865 := by
 decide +kernel
def cuts45866 : List PrefixCut := [⟨64,273813275,273813435⟩]
theorem checked45866 : checkPrefixCuts (2^48) 6015680513 10 Manual.Count131072.C045866.packed 64 cuts45866 = true := by
 decide +kernel
def cuts45867 : List PrefixCut := [⟨18,77716591,77716633⟩,
⟨64,274836652,274836807⟩]
theorem checked45867 : checkPrefixCuts (2^48) 6015811585 10 Manual.Count131072.C045867.packed 64 cuts45867 = true := by
 decide +kernel
def pointBounds45867 : List (Nat × Nat × Nat) := [(6015848448,110581192466496,110581578973271)]
theorem point_links_checked45867 : (cuts45867.take 1).map (fun c => (6015811585-1+2*2^10*c.k,110581114749905+c.lower,110581501256638+c.upper)) = pointBounds45867 := by
 decide +kernel
def cuts45868 : List PrefixCut := [⟨46,195385823,195385933⟩,
⟨64,270479417,270479571⟩]
theorem checked45868 : checkPrefixCuts (2^48) 6015942657 10 Manual.Count131072.C045868.packed 64 cuts45868 = true := by
 decide +kernel
def pointBounds45868 : List (Nat × Nat × Nat) := [(6016036864,110581584972380,110581971479378)]
theorem point_links_checked45868 : (cuts45868.take 1).map (fun c => (6015942657-1+2*2^10*c.k,110581389586557+c.lower,110581776093445+c.upper)) = pointBounds45868 := by
 decide +kernel
def cuts45869 : List PrefixCut := [⟨64,274731099,274731254⟩]
theorem checked45869 : checkPrefixCuts (2^48) 6016073729 10 Manual.Count131072.C045869.packed 64 cuts45869 = true := by
 decide +kernel
def cuts45870 : List PrefixCut := [⟨10,42388155,42388180⟩,
⟨64,273040823,273040978⟩]
theorem checked45870 : checkPrefixCuts (2^48) 6016204801 10 Manual.Count131072.C045870.packed 64 cuts45870 = true := by
 decide +kernel
def pointBounds45870 : List (Nat × Nat × Nat) := [(6016225280,110581977185228,110582363692450)]
theorem point_links_checked45870 : (cuts45870.take 1).map (fun c => (6016204801-1+2*2^10*c.k,110581934797073+c.lower,110582321304270+c.upper)) = pointBounds45870 := by
 decide +kernel
def cuts45871 : List PrefixCut := [⟨38,163793588,163793675⟩,
⟨64,271818517,271818664⟩]
theorem checked45871 : checkPrefixCuts (2^48) 6016335873 10 Manual.Count131072.C045871.packed 64 cuts45871 = true := by
 decide +kernel
def pointBounds45871 : List (Nat × Nat × Nat) := [(6016413696,110582371631484,110582758138923)]
theorem point_links_checked45871 : (cuts45871.take 1).map (fun c => (6016335873-1+2*2^10*c.k,110582207837896+c.lower,110582594345248+c.upper)) = pointBounds45871 := by
 decide +kernel
def cuts45872 : List PrefixCut := [⟨64,269660534,269660686⟩]
theorem checked45872 : checkPrefixCuts (2^48) 6016466945 10 Manual.Count131072.C045872.packed 64 cuts45872 = true := by
 decide +kernel
def cuts45873 : List PrefixCut := [⟨2,8654864,8654869⟩,
⟨64,273022970,273023131⟩]
theorem checked45873 : checkPrefixCuts (2^48) 6016598017 10 Manual.Count131072.C045873.packed 64 cuts45873 = true := by
 decide +kernel
def pointBounds45873 : List (Nat × Nat × Nat) := [(6016602112,110582757971811,110583144479467)]
theorem point_links_checked45873 : (cuts45873.take 1).map (fun c => (6016598017-1+2*2^10*c.k,110582749316947+c.lower,110583135824598+c.upper)) = pointBounds45873 := by
 decide +kernel
def cuts45874 : List PrefixCut := [⟨30,126778699,126778773⟩,
⟨64,270023036,270023191⟩]
theorem checked45874 : checkPrefixCuts (2^48) 6016729089 10 Manual.Count131072.C045874.packed 64 cuts45874 = true := by
 decide +kernel
def pointBounds45874 : List (Nat × Nat × Nat) := [(6016790528,110583149118616,110583535626502)]
theorem point_links_checked45874 : (cuts45874.take 1).map (fun c => (6016729089-1+2*2^10*c.k,110583022339917+c.lower,110583408847729+c.upper)) = pointBounds45874 := by
 decide +kernel
def cuts45875 : List PrefixCut := [⟨58,246346456,246346597⟩,
⟨64,272590068,272590225⟩]
theorem checked45875 : checkPrefixCuts (2^48) 6016860161 10 Manual.Count131072.C045875.packed 64 cuts45875 = true := by
 decide +kernel
def pointBounds45875 : List (Nat × Nat × Nat) := [(6016978944,110583538709409,110583925217517)]
theorem point_links_checked45875 : (cuts45875.take 1).map (fun c => (6016860161-1+2*2^10*c.k,110583292362953+c.lower,110583678870920+c.upper)) = pointBounds45875 := by
 decide +kernel
def cuts45876 : List PrefixCut := [⟨64,274595667,274595818⟩]
theorem checked45876 : checkPrefixCuts (2^48) 6016991233 10 Manual.Count131072.C045876.packed 64 cuts45876 = true := by
 decide +kernel
def cuts45877 : List PrefixCut := [⟨22,94633539,94633594⟩,
⟨64,276320456,276320613⟩]
theorem checked45877 : checkPrefixCuts (2^48) 6017122305 10 Manual.Count131072.C045877.packed 64 cuts45877 = true := by
 decide +kernel
def pointBounds45877 : List (Nat × Nat × Nat) := [(6017167360,110583934182227,110584320690557)]
theorem point_links_checked45877 : (cuts45877.take 1).map (fun c => (6017122305-1+2*2^10*c.k,110583839548688+c.lower,110584226056963+c.upper)) = pointBounds45877 := by
 decide +kernel
def cuts45878 : List PrefixCut := [⟨50,209844188,209844314⟩,
⟨64,270093046,270093209⟩]
theorem checked45878 : checkPrefixCuts (2^48) 6017253377 10 Manual.Count131072.C045878.packed 64 cuts45878 = true := by
 decide +kernel
def pointBounds45878 : List (Nat × Nat × Nat) := [(6017355776,110584325713332,110584712221890)]
theorem point_links_checked45878 : (cuts45878.take 1).map (fun c => (6017253377-1+2*2^10*c.k,110584115869144+c.lower,110584502377576+c.upper)) = pointBounds45878 := by
 decide +kernel
def cuts45879 : List PrefixCut := [⟨64,272145338,272145496⟩]
theorem checked45879 : checkPrefixCuts (2^48) 6017384449 10 Manual.Count131072.C045879.packed 64 cuts45879 = true := by
 decide +kernel
def cuts45880 : List PrefixCut := [⟨14,58984310,58984344⟩,
⟨64,269145788,269145943⟩]
theorem checked45880 : checkPrefixCuts (2^48) 6017515521 10 Manual.Count131072.C045880.packed 64 cuts45880 = true := by
 decide +kernel
def pointBounds45880 : List (Nat × Nat × Nat) := [(6017544192,110584717091838,110585103600625)]
theorem point_links_checked45880 : (cuts45880.take 1).map (fun c => (6017515521-1+2*2^10*c.k,110584658107528+c.lower,110585044616281+c.upper)) = pointBounds45880 := by
 decide +kernel
def cuts45881 : List PrefixCut := [⟨42,177275649,177275753⟩,
⟨64,271806043,271806203⟩]
theorem checked45881 : checkPrefixCuts (2^48) 6017646593 10 Manual.Count131072.C045881.packed 64 cuts45881 = true := by
 decide +kernel
def pointBounds45881 : List (Nat × Nat × Nat) := [(6017732608,110585104528965,110585491037977)]
theorem point_links_checked45881 : (cuts45881.take 1).map (fun c => (6017646593-1+2*2^10*c.k,110584927253316+c.lower,110585313762224+c.upper)) = pointBounds45881 := by
 decide +kernel
def cuts45882 : List PrefixCut := [⟨64,268479243,268479390⟩]
theorem checked45882 : checkPrefixCuts (2^48) 6017777665 10 Manual.Count131072.C045882.packed 64 cuts45882 = true := by
 decide +kernel
def cuts45883 : List PrefixCut := [⟨6,25491191,25491206⟩,
⟨64,271794211,271794369⟩]
theorem checked45883 : checkPrefixCuts (2^48) 6017908737 10 Manual.Count131072.C045883.packed 64 cuts45883 = true := by
 decide +kernel
def pointBounds45883 : List (Nat × Nat × Nat) := [(6017921024,110585493029793,110585879539023)]
theorem point_links_checked45883 : (cuts45883.take 1).map (fun c => (6017908737-1+2*2^10*c.k,110585467538602+c.lower,110585854047817+c.upper)) = pointBounds45883 := by
 decide +kernel
def cuts45884 : List PrefixCut := [⟨34,144570975,144571060⟩,
⟨64,273893006,273893163⟩]
theorem checked45884 : checkPrefixCuts (2^48) 6018039809 10 Manual.Count131072.C045884.packed 64 cuts45884 = true := by
 decide +kernel
def pointBounds45884 : List (Nat × Nat × Nat) := [(6018109440,110585883903788,110586270413246)]
theorem point_links_checked45884 : (cuts45884.take 1).map (fun c => (6018039809-1+2*2^10*c.k,110585739332813+c.lower,110586125842186+c.upper)) = pointBounds45884 := by
 decide +kernel
def cuts45885 : List PrefixCut := [⟨62,262288111,262288263⟩,
⟨64,270706681,270706838⟩]
theorem checked45885 : checkPrefixCuts (2^48) 6018170881 10 Manual.Count131072.C045885.packed 64 cuts45885 = true := by
 decide +kernel
def pointBounds45885 : List (Nat × Nat × Nat) := [(6018297856,110586275513930,110586662023612)]
theorem point_links_checked45885 : (cuts45885.take 1).map (fun c => (6018170881-1+2*2^10*c.k,110586013225819+c.lower,110586399735349+c.upper)) = pointBounds45885 := by
 decide +kernel
def cuts45886 : List PrefixCut := [⟨64,271215249,271215400⟩]
theorem checked45886 : checkPrefixCuts (2^48) 6018301953 10 Manual.Count131072.C045886.packed 64 cuts45886 = true := by
 decide +kernel
def cuts45887 : List PrefixCut := [⟨26,110888332,110888396⟩,
⟨64,272191461,272191619⟩]
theorem checked45887 : checkPrefixCuts (2^48) 6018433025 10 Manual.Count131072.C045887.packed 64 cuts45887 = true := by
 decide +kernel
def pointBounds45887 : List (Nat × Nat × Nat) := [(6018486272,110586666036081,110587052545983)]
theorem point_links_checked45887 : (cuts45887.take 1).map (fun c => (6018433025-1+2*2^10*c.k,110586555147749+c.lower,110586941657587+c.upper)) = pointBounds45887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000183
