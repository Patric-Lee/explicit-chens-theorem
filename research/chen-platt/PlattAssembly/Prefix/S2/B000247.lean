import PlattAssemblyKernel
import PlattCertificates.Count131072.C017904
import PlattCertificates.Count131072.C017905
import PlattCertificates.Count131072.C017906
import PlattCertificates.Count131072.C017907
import PlattCertificates.Count131072.C017908
import PlattCertificates.Count131072.C017909
import PlattCertificates.Count131072.C017910
import PlattCertificates.Count131072.C017911
import PlattCertificates.Count131072.C017912
import PlattCertificates.Count131072.C017913
import PlattCertificates.Count131072.C017914
import PlattCertificates.Count131072.C017915
import PlattCertificates.Count131072.C017916
import PlattCertificates.Count131072.C017917
import PlattCertificates.Count131072.C017918
import PlattCertificates.Count131072.C017919
import PlattCertificates.Count131072.C017920
import PlattCertificates.Count131072.C017921
import PlattCertificates.Count131072.C017922
import PlattCertificates.Count131072.C017923
import PlattCertificates.Count131072.C017924
import PlattCertificates.Count131072.C017925
import PlattCertificates.Count131072.C017926
import PlattCertificates.Count131072.C017927
import PlattCertificates.Count131072.C017928
import PlattCertificates.Count131072.C017929
import PlattCertificates.Count131072.C017930
import PlattCertificates.Count131072.C017931
import PlattCertificates.Count131072.C017932
import PlattCertificates.Count131072.C017933
import PlattCertificates.Count131072.C017934
import PlattCertificates.Count131072.C017935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17904 : List PrefixCut := [⟨28,159138357,159138457⟩,
⟨100,563980419,563980765⟩,
⟨128,725267147,725267595⟩]
theorem checked17904 : checkPrefixCuts (2^48) 2350645249 9 Manual.Count131072.C017904.packed 128 cuts17904 = true := by
 decide +kernel
def pointBounds17904 : List (Nat × Nat × Nat) := [(2350673920,98582793578393,98583173086489),(2350747648,98583198420455,98583577928797)]
theorem point_links_checked17904 : (cuts17904.take 2).map (fun c => (2350645249-1+2*2^9*c.k,98582634440036+c.lower,98583013948032+c.upper)) = pointBounds17904 := by
 decide +kernel
def cuts17905 : List PrefixCut := [⟨44,247613735,247613888⟩,
⟨116,656142038,656142445⟩,
⟨128,724987150,724987602⟩]
theorem checked17905 : checkPrefixCuts (2^48) 2350776321 9 Manual.Count131072.C017905.packed 128 cuts17905 = true := by
 decide +kernel
def pointBounds17905 : List (Nat × Nat × Nat) := [(2350821376,98583607320918,98583986829515),(2350895104,98584015849221,98584395358072)]
theorem point_links_checked17905 : (cuts17905.take 2).map (fun c => (2350776321-1+2*2^9*c.k,98583359707183+c.lower,98583739215627+c.upper)) = pointBounds17905 := by
 decide +kernel
def cuts17906 : List PrefixCut := [⟨60,346495027,346495243⟩,
⟨128,737039354,737039806⟩]
theorem checked17906 : checkPrefixCuts (2^48) 2350907393 9 Manual.Count131072.C017906.packed 128 cuts17906 = true := by
 decide +kernel
def pointBounds17906 : List (Nat × Nat × Nat) := [(2350968832,98584431189360,98584810698472)]
theorem point_links_checked17906 : (cuts17906.take 1).map (fun c => (2350907393-1+2*2^9*c.k,98584084694333+c.lower,98584464203229+c.upper)) = pointBounds17906 := by
 decide +kernel
def cuts17907 : List PrefixCut := [⟨4,22627749,22627764⟩,
⟨76,424532999,424533253⟩,
⟨128,721673882,721674318⟩]
theorem checked17907 : checkPrefixCuts (2^48) 2351038465 9 Manual.Count131072.C017907.packed 128 cuts17907 = true := by
 decide +kernel
def pointBounds17907 : List (Nat × Nat × Nat) := [(2351042560,98584844361436,98585223870799),(2351116288,98585246266686,98585625776288)]
theorem point_links_checked17907 : (cuts17907.take 2).map (fun c => (2351038465-1+2*2^9*c.k,98584821733687+c.lower,98585201243035+c.upper)) = pointBounds17907 := by
 decide +kernel
def cuts17908 : List PrefixCut := [⟨20,112533451,112533521⟩,
⟨92,518962681,518963005⟩,
⟨128,723788601,723789048⟩]
theorem checked17908 : checkPrefixCuts (2^48) 2351169537 9 Manual.Count131072.C017908.packed 128 cuts17908 = true := by
 decide +kernel
def pointBounds17908 : List (Nat × Nat × Nat) := [(2351190016,98585655941020,98586035450874),(2351263744,98586062370250,98586441880358)]
theorem point_links_checked17908 : (cuts17908.take 2).map (fun c => (2351169537-1+2*2^9*c.k,98585543407569+c.lower,98585922917353+c.upper)) = pointBounds17908 := by
 decide +kernel
def cuts17909 : List PrefixCut := [⟨36,199435826,199435945⟩,
⟨108,613979644,613980013⟩,
⟨128,726022717,726023157⟩]
theorem checked17909 : checkPrefixCuts (2^48) 2351300609 9 Manual.Count131072.C017909.packed 128 cuts17909 = true := by
 decide +kernel
def pointBounds17909 : List (Nat × Nat × Nat) := [(2351337472,98586466631996,98586846142346),(2351411200,98586881175814,98587260686414)]
theorem point_links_checked17909 : (cuts17909.take 2).map (fun c => (2351300609-1+2*2^9*c.k,98586267196170+c.lower,98586646706401+c.upper)) = pointBounds17909 := by
 decide +kernel
def cuts17910 : List PrefixCut := [⟨52,296981306,296981482⟩,
⟨124,707788367,707788786⟩,
⟨128,729692928,729693361⟩]
theorem checked17910 : checkPrefixCuts (2^48) 2351431681 9 Manual.Count131072.C017910.packed 128 cuts17910 = true := by
 decide +kernel
def pointBounds17910 : List (Nat × Nat × Nat) := [(2351484928,98587290200193,98587669711040),(2351558656,98587701007254,98588080518344)]
theorem point_links_checked17910 : (cuts17910.take 2).map (fun c => (2351431681-1+2*2^9*c.k,98586993218887+c.lower,98587372729558+c.upper)) = pointBounds17910 := by
 decide +kernel
def cuts17911 : List PrefixCut := [⟨68,380391366,380391604⟩,
⟨128,719478396,719478839⟩]
theorem checked17911 : checkPrefixCuts (2^48) 2351562753 9 Manual.Count131072.C017911.packed 128 cuts17911 = true := by
 decide +kernel
def pointBounds17911 : List (Nat × Nat × Nat) := [(2351632384,98588103303181,98588482814523)]
theorem point_links_checked17911 : (cuts17911.take 1).map (fun c => (2351562753-1+2*2^9*c.k,98587722911815+c.lower,98588102422919+c.upper)) = pointBounds17911 := by
 decide +kernel
def cuts17912 : List PrefixCut := [⟨12,69539870,69539911⟩,
⟨84,478273657,478273946⟩,
⟨128,732364384,732364827⟩]
theorem checked17912 : checkPrefixCuts (2^48) 2351693825 9 Manual.Count131072.C017912.packed 128 cuts17912 = true := by
 decide +kernel
def pointBounds17912 : List (Nat × Nat × Nat) := [(2351706112,98588511930081,98588891441669),(2351779840,98588920663868,98589300175704)]
theorem point_links_checked17912 : (cuts17912.take 2).map (fun c => (2351693825-1+2*2^9*c.k,98588442390211+c.lower,98588821901758+c.upper)) = pointBounds17912 := by
 decide +kernel
def cuts17913 : List PrefixCut := [⟨28,151877563,151877656⟩,
⟨100,561423426,561423768⟩,
⟨128,723586649,723587092⟩]
theorem checked17913 : checkPrefixCuts (2^48) 2351824897 9 Manual.Count131072.C017913.packed 128 cuts17913 = true := by
 decide +kernel
def pointBounds17913 : List (Nat × Nat × Nat) := [(2351853568,98589326632158,98589706144241),(2351927296,98589736178021,98590115690353)]
theorem point_links_checked17913 : (cuts17913.take 2).map (fun c => (2351824897-1+2*2^9*c.k,98589174754595+c.lower,98589554266585+c.upper)) = pointBounds17913 := by
 decide +kernel
def cuts17914 : List PrefixCut := [⟨44,250481435,250481588⟩,
⟨116,650906549,650906947⟩,
⟨128,716725366,716725805⟩]
theorem checked17914 : checkPrefixCuts (2^48) 2351955969 9 Manual.Count131072.C017914.packed 128 cuts17914 = true := by
 decide +kernel
def pointBounds17914 : List (Nat × Nat × Nat) := [(2352001024,98590148822679,98590528335265),(2352074752,98590549247793,98590928760624)]
theorem point_links_checked17914 : (cuts17914.take 2).map (fun c => (2351955969-1+2*2^9*c.k,98589898341244+c.lower,98590277853677+c.upper)) = pointBounds17914 := by
 decide +kernel
def cuts17915 : List PrefixCut := [⟨60,340337831,340338042⟩,
⟨128,731404257,731404710⟩]
theorem checked17915 : checkPrefixCuts (2^48) 2352087041 9 Manual.Count131072.C017915.packed 128 cuts17915 = true := by
 decide +kernel
def pointBounds17915 : List (Nat × Nat × Nat) := [(2352148480,98590955404441,98591334917524)]
theorem point_links_checked17915 : (cuts17915.take 1).map (fun c => (2352087041-1+2*2^9*c.k,98590615066610+c.lower,98590994579482+c.upper)) = pointBounds17915 := by
 decide +kernel
def cuts17916 : List PrefixCut := [⟨4,20342794,20342806⟩,
⟨76,432457128,432457399⟩,
⟨128,723705459,723705905⟩]
theorem checked17916 : checkPrefixCuts (2^48) 2352218113 9 Manual.Count131072.C017916.packed 128 cuts17916 = true := by
 decide +kernel
def pointBounds17916 : List (Nat × Nat × Nat) := [(2352222208,98591366813661,98591746326998),(2352295936,98591778927995,98592158441591)]
theorem point_links_checked17916 : (cuts17916.take 2).map (fun c => (2352218113-1+2*2^9*c.k,98591346470867+c.lower,98591725984192+c.upper)) = pointBounds17916 := by
 decide +kernel
def cuts17917 : List PrefixCut := [⟨20,118340182,118340253⟩,
⟨92,526240710,526241031⟩,
⟨128,729288805,729289251⟩]
theorem checked17917 : checkPrefixCuts (2^48) 2352349185 9 Manual.Count131072.C017917.packed 128 cuts17917 = true := by
 decide +kernel
def pointBounds17917 : List (Nat × Nat × Nat) := [(2352369664,98592188516508,98592568030350),(2352443392,98592596417036,98592975931128)]
theorem point_links_checked17917 : (cuts17917.take 2).map (fun c => (2352349185-1+2*2^9*c.k,98592070176326+c.lower,98592449690097+c.upper)) = pointBounds17917 := by
 decide +kernel
def cuts17918 : List PrefixCut := [⟨36,204719989,204720111⟩,
⟨108,611039492,611039866⟩,
⟨128,724462112,724462555⟩]
theorem checked17918 : checkPrefixCuts (2^48) 2352480257 9 Manual.Count131072.C017918.packed 128 cuts17918 = true := by
 decide +kernel
def pointBounds17918 : List (Nat × Nat × Nat) := [(2352517120,98593004185120,98593383699459),(2352590848,98593410504623,98593790019214)]
theorem point_links_checked17918 : (cuts17918.take 2).map (fun c => (2352480257-1+2*2^9*c.k,98592799465131+c.lower,98593178979348+c.upper)) = pointBounds17918 := by
 decide +kernel
def cuts17919 : List PrefixCut := [⟨52,290969963,290970143⟩,
⟨124,708749381,708749822⟩,
⟨128,731480418,731480873⟩]
theorem checked17919 : checkPrefixCuts (2^48) 2352611329 9 Manual.Count131072.C017919.packed 128 cuts17919 = true := by
 decide +kernel
def pointBounds17919 : List (Nat × Nat × Nat) := [(2352664576,98593814897206,98594194412046),(2352738304,98594232676624,98594612191725)]
theorem point_links_checked17919 : (cuts17919.take 2).map (fun c => (2352611329-1+2*2^9*c.k,98593523927243+c.lower,98593903441903+c.upper)) = pointBounds17919 := by
 decide +kernel
def cuts17920 : List PrefixCut := [⟨68,392762222,392762463⟩,
⟨128,732516653,732517105⟩]
theorem checked17920 : checkPrefixCuts (2^48) 2352742401 9 Manual.Count131072.C017920.packed 128 cuts17920 = true := by
 decide +kernel
def pointBounds17920 : List (Nat × Nat × Nat) := [(2352812032,98594648169883,98595027685239)]
theorem point_links_checked17920 : (cuts17920.take 1).map (fun c => (2352742401-1+2*2^9*c.k,98594255407661+c.lower,98594634922776+c.upper)) = pointBounds17920 := by
 decide +kernel
def cuts17921 : List PrefixCut := [⟨12,69505015,69505056⟩,
⟨84,482340504,482340795⟩,
⟨128,741208472,741208918⟩]
theorem checked17921 : checkPrefixCuts (2^48) 2352873473 9 Manual.Count131072.C017921.packed 128 cuts17921 = true := by
 decide +kernel
def pointBounds17921 : List (Nat × Nat × Nat) := [(2352885760,98595057429329,98595436944937),(2352959488,98595470264818,98595849780676)]
theorem point_links_checked17921 : (cuts17921.take 2).map (fun c => (2352873473-1+2*2^9*c.k,98594987924314+c.lower,98595367439881+c.upper)) = pointBounds17921 := by
 decide +kernel
def cuts17922 : List PrefixCut := [⟨28,162328230,162328329⟩,
⟨100,570472601,570472950⟩,
⟨128,727889463,727889912⟩]
theorem checked17922 : checkPrefixCuts (2^48) 2353004545 9 Manual.Count131072.C017922.packed 128 cuts17922 = true := by
 decide +kernel
def pointBounds17922 : List (Nat × Nat × Nat) := [(2353033216,98595891461016,98596270977128),(2353106944,98596299605387,98596679121749)]
theorem point_links_checked17922 : (cuts17922.take 2).map (fun c => (2353004545-1+2*2^9*c.k,98595729132786+c.lower,98596108648799+c.upper)) = pointBounds17922 := by
 decide +kernel
def cuts17923 : List PrefixCut := [⟨44,247245873,247246029⟩,
⟨116,659670762,659671170⟩,
⟨128,727489968,727490415⟩]
theorem checked17923 : checkPrefixCuts (2^48) 2353135617 9 Manual.Count131072.C017923.packed 128 cuts17923 = true := by
 decide +kernel
def pointBounds17923 : List (Nat × Nat × Nat) := [(2353180672,98596704268122,98597083784740),(2353254400,98597116693011,98597496209881)]
theorem point_links_checked17923 : (cuts17923.take 2).map (fun c => (2353135617-1+2*2^9*c.k,98596457022249+c.lower,98596836538711+c.upper)) = pointBounds17923 := by
 decide +kernel
def cuts17924 : List PrefixCut := [⟨60,337176932,337177137⟩,
⟨128,720392635,720393078⟩]
theorem checked17924 : checkPrefixCuts (2^48) 2353266689 9 Manual.Count131072.C017924.packed 128 cuts17924 = true := by
 decide +kernel
def pointBounds17924 : List (Nat × Nat × Nat) := [(2353328128,98597521689149,98597901206263)]
theorem point_links_checked17924 : (cuts17924.take 1).map (fun c => (2353266689-1+2*2^9*c.k,98597184512217+c.lower,98597564029126+c.upper)) = pointBounds17924 := by
 decide +kernel
def cuts17925 : List PrefixCut := [⟨4,23561892,23561907⟩,
⟨76,432838320,432838583⟩,
⟨128,724538620,724539065⟩]
theorem checked17925 : checkPrefixCuts (2^48) 2353397761 9 Manual.Count131072.C017925.packed 128 cuts17925 = true := by
 decide +kernel
def pointBounds17925 : List (Nat × Nat × Nat) := [(2353401856,98597928466744,98598307984111),(2353475584,98598337743172,98598717260787)]
theorem point_links_checked17925 : (cuts17925.take 2).map (fun c => (2353397761-1+2*2^9*c.k,98597904904852+c.lower,98598284422204+c.upper)) = pointBounds17925 := by
 decide +kernel
def cuts17926 : List PrefixCut := [⟨20,112301052,112301120⟩,
⟨92,526455226,526455541⟩,
⟨128,729640715,729641156⟩]
theorem checked17926 : checkPrefixCuts (2^48) 2353528833 9 Manual.Count131072.C017926.packed 128 cuts17926 = true := by
 decide +kernel
def pointBounds17926 : List (Nat × Nat × Nat) := [(2353549312,98598741744524,98599121262389),(2353623040,98599155898698,98599535416810)]
theorem point_links_checked17926 : (cuts17926.take 2).map (fun c => (2353528833-1+2*2^9*c.k,98598629443472+c.lower,98599008961269+c.upper)) = pointBounds17926 := by
 decide +kernel
def cuts17927 : List PrefixCut := [⟨36,209400975,209401109⟩,
⟨108,617310740,617311125⟩,
⟨128,728165264,728165717⟩]
theorem checked17927 : checkPrefixCuts (2^48) 2353659905 9 Manual.Count131072.C017927.packed 128 cuts17927 = true := by
 decide +kernel
def pointBounds17927 : List (Nat × Nat × Nat) := [(2353696768,98599568485162,98599948003534),(2353770496,98599976394927,98600355913550)]
theorem point_links_checked17927 : (cuts17927.take 2).map (fun c => (2353659905-1+2*2^9*c.k,98599359084187+c.lower,98599738602425+c.upper)) = pointBounds17927 := by
 decide +kernel
def cuts17928 : List PrefixCut := [⟨52,297042421,297042598⟩,
⟨124,702295948,702296374⟩,
⟨128,725135171,725135611⟩]
theorem checked17928 : checkPrefixCuts (2^48) 2353790977 9 Manual.Count131072.C017928.packed 128 cuts17928 = true := by
 decide +kernel
def pointBounds17928 : List (Nat × Nat × Nat) := [(2353844224,98600384291872,98600763810740),(2353917952,98600789545399,98601169064516)]
theorem point_links_checked17928 : (cuts17928.take 2).map (fun c => (2353790977-1+2*2^9*c.k,98600087249451+c.lower,98600466768142+c.upper)) = pointBounds17928 := by
 decide +kernel
def cuts17929 : List PrefixCut := [⟨68,384434258,384434493⟩,
⟨128,726768602,726769046⟩]
theorem checked17929 : checkPrefixCuts (2^48) 2353922049 9 Manual.Count131072.C017929.packed 128 cuts17929 = true := by
 decide +kernel
def pointBounds17929 : List (Nat × Nat × Nat) := [(2353991680,98601196818880,98601576338246)]
theorem point_links_checked17929 : (cuts17929.take 1).map (fun c => (2353922049-1+2*2^9*c.k,98600812384622+c.lower,98601191903753+c.upper)) = pointBounds17929 := by
 decide +kernel
def cuts17930 : List PrefixCut := [⟨12,64328665,64328706⟩,
⟨84,464761315,464761599⟩,
⟨128,716086569,716087003⟩]
theorem checked17930 : checkPrefixCuts (2^48) 2354053121 9 Manual.Count131072.C017930.packed 128 cuts17930 = true := by
 decide +kernel
def pointBounds17930 : List (Nat × Nat × Nat) := [(2354065408,98601603481889,98601983001505),(2354139136,98602003914539,98602383434398)]
theorem point_links_checked17930 : (cuts17930.take 2).map (fun c => (2354053121-1+2*2^9*c.k,98601539153224+c.lower,98601918672799+c.upper)) = pointBounds17930 := by
 decide +kernel
def cuts17931 : List PrefixCut := [⟨28,158181770,158181867⟩,
⟨100,568273743,568274094⟩,
⟨128,727165972,727166414⟩]
theorem checked17931 : checkPrefixCuts (2^48) 2354184193 9 Manual.Count131072.C017931.packed 128 cuts17931 = true := by
 decide +kernel
def pointBounds17931 : List (Nat × Nat × Nat) := [(2354212864,98602413421563,98602792941669),(2354286592,98602823513536,98603203033896)]
theorem point_links_checked17931 : (cuts17931.take 2).map (fun c => (2354184193-1+2*2^9*c.k,98602255239793+c.lower,98602634759802+c.upper)) = pointBounds17931 := by
 decide +kernel
def cuts17932 : List PrefixCut := [⟨44,249034863,249035012⟩,
⟨116,663644182,663644582⟩,
⟨128,733342225,733342666⟩]
theorem checked17932 : checkPrefixCuts (2^48) 2354315265 9 Manual.Count131072.C017932.packed 128 cuts17932 = true := by
 decide +kernel
def pointBounds17932 : List (Nat × Nat × Nat) := [(2354360320,98603231440628,98603610961228),(2354434048,98603646049947,98604025570798)]
theorem point_links_checked17932 : (cuts17932.take 2).map (fun c => (2354315265-1+2*2^9*c.k,98602982405765+c.lower,98603361926216+c.upper)) = pointBounds17932 := by
 decide +kernel
def cuts17933 : List PrefixCut := [⟨60,337725278,337725490⟩,
⟨128,720031671,720032120⟩]
theorem checked17933 : checkPrefixCuts (2^48) 2354446337 9 Manual.Count131072.C017933.packed 128 cuts17933 = true := by
 decide +kernel
def pointBounds17933 : List (Nat × Nat × Nat) := [(2354507776,98604053473268,98604432994372)]
theorem point_links_checked17933 : (cuts17933.take 1).map (fun c => (2354446337-1+2*2^9*c.k,98603715747990+c.lower,98604095268882+c.upper)) = pointBounds17933 := by
 decide +kernel
def cuts17934 : List PrefixCut := [⟨4,23789176,23789190⟩,
⟨76,441467547,441467808⟩,
⟨128,730750462,730750895⟩]
theorem checked17934 : checkPrefixCuts (2^48) 2354577409 9 Manual.Count131072.C017934.packed 128 cuts17934 = true := by
 decide +kernel
def pointBounds17934 : List (Nat × Nat × Nat) := [(2354581504,98604459568837,98604839090192),(2354655232,98604877247208,98605256768810)]
theorem point_links_checked17934 : (cuts17934.take 2).map (fun c => (2354577409-1+2*2^9*c.k,98604435779661+c.lower,98604815301002+c.upper)) = pointBounds17934 := by
 decide +kernel
def cuts17935 : List PrefixCut := [⟨20,114755056,114755129⟩,
⟨92,520812519,520812837⟩,
⟨128,725211092,725211534⟩]
theorem checked17935 : checkPrefixCuts (2^48) 2354708481 9 Manual.Count131072.C017935.packed 128 cuts17935 = true := by
 decide +kernel
def pointBounds17935 : List (Nat × Nat × Nat) := [(2354728960,98605281285179,98605660807026),(2354802688,98605687342642,98606066864734)]
theorem point_links_checked17935 : (cuts17935.take 2).map (fun c => (2354708481-1+2*2^9*c.k,98605166530123+c.lower,98605546051897+c.upper)) = pointBounds17935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000247
