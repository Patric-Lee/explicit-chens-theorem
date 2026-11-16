import PlattAssemblyKernel
import PlattCertificates.Count131072.C023936
import PlattCertificates.Count131072.C023937
import PlattCertificates.Count131072.C023938
import PlattCertificates.Count131072.C023939
import PlattCertificates.Count131072.C023940
import PlattCertificates.Count131072.C023941
import PlattCertificates.Count131072.C023942
import PlattCertificates.Count131072.C023943
import PlattCertificates.Count131072.C023944
import PlattCertificates.Count131072.C023945
import PlattCertificates.Count131072.C023946
import PlattCertificates.Count131072.C023947
import PlattCertificates.Count131072.C023948
import PlattCertificates.Count131072.C023949
import PlattCertificates.Count131072.C023950
import PlattCertificates.Count131072.C023951
import PlattCertificates.Count131072.C023952
import PlattCertificates.Count131072.C023953
import PlattCertificates.Count131072.C023954
import PlattCertificates.Count131072.C023955
import PlattCertificates.Count131072.C023956
import PlattCertificates.Count131072.C023957
import PlattCertificates.Count131072.C023958
import PlattCertificates.Count131072.C023959
import PlattCertificates.Count131072.C023960
import PlattCertificates.Count131072.C023961
import PlattCertificates.Count131072.C023962
import PlattCertificates.Count131072.C023963
import PlattCertificates.Count131072.C023964
import PlattCertificates.Count131072.C023965
import PlattCertificates.Count131072.C023966
import PlattCertificates.Count131072.C023967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23936 : List PrefixCut := [⟨63,260121795,260121939⟩,
⟨128,535022602,535022906⟩]
theorem checked23936 : checkPrefixCuts (2^48) 3141271553 9 Manual.Count131072.C023936.packed 128 cuts23936 = true := by
 decide +kernel
def pointBounds23936 : List (Nat × Nat × Nat) := [(3141336064,102339720400693,102340102102739)]
theorem point_links_checked23936 : (cuts23936.take 1).map (fun c => (3141271553-1+2*2^9*c.k,102339460278898+c.lower,102339841980800+c.upper)) = pointBounds23936 := by
 decide +kernel
def cuts23937 : List PrefixCut := [⟨31,129204951,129205024⟩,
⟨127,538763621,538763918⟩,
⟨128,542974724,542975023⟩]
theorem checked23937 : checkPrefixCuts (2^48) 3141402625 9 Manual.Count131072.C023937.packed 128 cuts23937 = true := by
 decide +kernel
def pointBounds23937 : List (Nat × Nat × Nat) := [(3141434368,102340124506451,102340506208730),(3141532672,102340534065121,102340915767624)]
theorem point_links_checked23937 : (cuts23937.take 2).map (fun c => (3141402625-1+2*2^9*c.k,102339995301500+c.lower,102340377003706+c.upper)) = pointBounds23937 := by
 decide +kernel
def cuts23938 : List PrefixCut := [⟨95,402646797,402647031⟩,
⟨128,546087863,546088172⟩]
theorem checked23938 : checkPrefixCuts (2^48) 3141533697 9 Manual.Count131072.C023938.packed 128 cuts23938 = true := by
 decide +kernel
def pointBounds23938 : List (Nat × Nat × Nat) := [(3141630976,102340940923021,102341322625760)]
theorem point_links_checked23938 : (cuts23938.take 1).map (fun c => (3141533697-1+2*2^9*c.k,102340538276224+c.lower,102340919978729+c.upper)) = pointBounds23938 := by
 decide +kernel
def cuts23939 : List PrefixCut := [⟨63,265285692,265285845⟩,
⟨128,537374756,537375065⟩]
theorem checked23939 : checkPrefixCuts (2^48) 3141664769 9 Manual.Count131072.C023939.packed 128 cuts23939 = true := by
 decide +kernel
def pointBounds23939 : List (Nat × Nat × Nat) := [(3141729280,102341349649779,102341731352746)]
theorem point_links_checked23939 : (cuts23939.take 1).map (fun c => (3141664769-1+2*2^9*c.k,102341084364087+c.lower,102341466066901+c.upper)) = pointBounds23939 := by
 decide +kernel
def cuts23940 : List PrefixCut := [⟨31,127128215,127128282⟩,
⟨127,533052041,533052337⟩,
⟨128,538068898,538069196⟩]
theorem checked23940 : checkPrefixCuts (2^48) 3141795841 9 Manual.Count131072.C023940.packed 128 cuts23940 = true := by
 decide +kernel
def pointBounds23940 : List (Nat × Nat × Nat) := [(3141827584,102341748867058,102342130570248),(3141925888,102342154790884,102342536494303)]
theorem point_links_checked23940 : (cuts23940.take 2).map (fun c => (3141795841-1+2*2^9*c.k,102341621738843+c.lower,102342003441966+c.upper)) = pointBounds23940 := by
 decide +kernel
def cuts23941 : List PrefixCut := [⟨95,400088076,400088301⟩,
⟨128,538046593,538046897⟩]
theorem checked23941 : checkPrefixCuts (2^48) 3141926913 9 Manual.Count131072.C023941.packed 128 cuts23941 = true := by
 decide +kernel
def pointBounds23941 : List (Nat × Nat × Nat) := [(3142024192,102342559895817,102342941599463)]
theorem point_links_checked23941 : (cuts23941.take 1).map (fun c => (3141926913-1+2*2^9*c.k,102342159807741+c.lower,102342541511162+c.upper)) = pointBounds23941 := by
 decide +kernel
def cuts23942 : List PrefixCut := [⟨63,258085874,258086023⟩,
⟨128,528259733,528260037⟩]
theorem checked23942 : checkPrefixCuts (2^48) 3142057985 9 Manual.Count131072.C023942.packed 128 cuts23942 = true := by
 decide +kernel
def pointBounds23942 : List (Nat × Nat × Nat) := [(3142122496,102342955940208,102343337644082)]
theorem point_links_checked23942 : (cuts23942.take 1).map (fun c => (3142057985-1+2*2^9*c.k,102342697854334+c.lower,102343079558059+c.upper)) = pointBounds23942 := by
 decide +kernel
def cuts23943 : List PrefixCut := [⟨31,131232925,131233000⟩,
⟨127,535135299,535135603⟩,
⟨128,539434924,539435230⟩]
theorem checked23943 : checkPrefixCuts (2^48) 3142189057 9 Manual.Count131072.C023943.packed 128 cuts23943 = true := by
 decide +kernel
def pointBounds23943 : List (Nat × Nat × Nat) := [(3142220800,102343357346992,102343739051096),(3142319104,102343761249366,102344142953699)]
theorem point_links_checked23943 : (cuts23943.take 2).map (fun c => (3142189057-1+2*2^9*c.k,102343226114067+c.lower,102343607818096+c.upper)) = pointBounds23943 := by
 decide +kernel
def cuts23944 : List PrefixCut := [⟨95,390005671,390005886⟩,
⟨128,531440250,531440538⟩]
theorem checked23944 : checkPrefixCuts (2^48) 3142320129 9 Manual.Count131072.C023944.packed 128 cuts23944 = true := by
 decide +kernel
def pointBounds23944 : List (Nat × Nat × Nat) := [(3142417408,102344155554662,102344537259212)]
theorem point_links_checked23944 : (cuts23944.take 1).map (fun c => (3142320129-1+2*2^9*c.k,102343765548991+c.lower,102344147253326+c.upper)) = pointBounds23944 := by
 decide +kernel
def cuts23945 : List PrefixCut := [⟨63,261994707,261994860⟩,
⟨128,534911380,534911686⟩]
theorem checked23945 : checkPrefixCuts (2^48) 3142451201 9 Manual.Count131072.C023945.packed 128 cuts23945 = true := by
 decide +kernel
def pointBounds23945 : List (Nat × Nat × Nat) := [(3142515712,102344558983948,102344940688724)]
theorem point_links_checked23945 : (cuts23945.take 1).map (fun c => (3142451201-1+2*2^9*c.k,102344296989241+c.lower,102344678693864+c.upper)) = pointBounds23945 := by
 decide +kernel
def cuts23946 : List PrefixCut := [⟨31,131037368,131037443⟩,
⟨127,532023170,532023474⟩,
⟨128,536143128,536143434⟩]
theorem checked23946 : checkPrefixCuts (2^48) 3142582273 9 Manual.Count131072.C023946.packed 128 cuts23946 = true := by
 decide +kernel
def pointBounds23946 : List (Nat × Nat × Nat) := [(3142614016,102344962937989,102345344642993),(3142712320,102345363923791,102345745629024)]
theorem point_links_checked23946 : (cuts23946.take 2).map (fun c => (3142582273-1+2*2^9*c.k,102344831900621+c.lower,102345213605550+c.upper)) = pointBounds23946 := by
 decide +kernel
def cuts23947 : List PrefixCut := [⟨95,401420940,401421159⟩,
⟨128,537643262,537643563⟩]
theorem checked23947 : checkPrefixCuts (2^48) 3142713345 9 Manual.Count131072.C023947.packed 128 cuts23947 = true := by
 decide +kernel
def pointBounds23947 : List (Nat × Nat × Nat) := [(3142810624,102345769464689,102346151170143)]
theorem point_links_checked23947 : (cuts23947.take 1).map (fun c => (3142713345-1+2*2^9*c.k,102345368043749+c.lower,102345749748984+c.upper)) = pointBounds23947 := by
 decide +kernel
def cuts23948 : List PrefixCut := [⟨63,263484464,263484609⟩,
⟨128,539232851,539233144⟩]
theorem checked23948 : checkPrefixCuts (2^48) 3142844417 9 Manual.Count131072.C023948.packed 128 cuts23948 = true := by
 decide +kernel
def pointBounds23948 : List (Nat × Nat × Nat) := [(3142908928,102346169171475,102346550877156)]
theorem point_links_checked23948 : (cuts23948.take 1).map (fun c => (3142844417-1+2*2^9*c.k,102345905687011+c.lower,102346287392547+c.upper)) = pointBounds23948 := by
 decide +kernel
def cuts23949 : List PrefixCut := [⟨31,136125683,136125761⟩,
⟨127,535986609,535986914⟩,
⟨128,540553817,540554125⟩]
theorem checked23949 : checkPrefixCuts (2^48) 3142975489 9 Manual.Count131072.C023949.packed 128 cuts23949 = true := by
 decide +kernel
def pointBounds23949 : List (Nat × Nat × Nat) := [(3143007232,102346581045545,102346962751452),(3143105536,102346980906471,102347362612605)]
theorem point_links_checked23949 : (cuts23949.take 2).map (fun c => (3142975489-1+2*2^9*c.k,102346444919862+c.lower,102346826625691+c.upper)) = pointBounds23949 := by
 decide +kernel
def cuts23950 : List PrefixCut := [⟨95,394654375,394654597⟩,
⟨128,534173016,534173317⟩]
theorem checked23950 : checkPrefixCuts (2^48) 3143106561 9 Manual.Count131072.C023950.packed 128 cuts23950 = true := by
 decide +kernel
def pointBounds23950 : List (Nat × Nat × Nat) := [(3143203840,102347380128054,102347761834413)]
theorem point_links_checked23950 : (cuts23950.take 1).map (fun c => (3143106561-1+2*2^9*c.k,102346985473679+c.lower,102347367179816+c.upper)) = pointBounds23950 := by
 decide +kernel
def cuts23951 : List PrefixCut := [⟨63,264526067,264526222⟩,
⟨128,534508950,534509255⟩]
theorem checked23951 : checkPrefixCuts (2^48) 3143237633 9 Manual.Count131072.C023951.packed 128 cuts23951 = true := by
 decide +kernel
def pointBounds23951 : List (Nat × Nat × Nat) := [(3143302144,102347784172762,102348165879355)]
theorem point_links_checked23951 : (cuts23951.take 1).map (fun c => (3143237633-1+2*2^9*c.k,102347519646695+c.lower,102347901353133+c.upper)) = pointBounds23951 := by
 decide +kernel
def cuts23952 : List PrefixCut := [⟨31,125363235,125363308⟩,
⟨127,520965663,520965959⟩,
⟨128,525174132,525174431⟩]
theorem checked23952 : checkPrefixCuts (2^48) 3143368705 9 Manual.Count131072.C023952.packed 128 cuts23952 = true := by
 decide +kernel
def pointBounds23952 : List (Nat × Nat × Nat) := [(3143400448,102348179518880,102348561225696),(3143498752,102348575121308,102348956828347)]
theorem point_links_checked23952 : (cuts23952.take 2).map (fun c => (3143368705-1+2*2^9*c.k,102348054155645+c.lower,102348435862388+c.upper)) = pointBounds23952 := by
 decide +kernel
def cuts23953 : List PrefixCut := [⟨95,396664422,396664650⟩,
⟨128,539568077,539568383⟩]
theorem checked23953 : checkPrefixCuts (2^48) 3143499777 9 Manual.Count131072.C023953.packed 128 cuts23953 = true := by
 decide +kernel
def pointBounds23953 : List (Nat × Nat × Nat) := [(3143597056,102348975994199,102349357701469)]
theorem point_links_checked23953 : (cuts23953.take 1).map (fun c => (3143499777-1+2*2^9*c.k,102348579329777+c.lower,102348961036819+c.upper)) = pointBounds23953 := by
 decide +kernel
def cuts23954 : List PrefixCut := [⟨63,267447727,267447875⟩,
⟨128,542142219,542142524⟩]
theorem checked23954 : checkPrefixCuts (2^48) 3143630849 9 Manual.Count131072.C023954.packed 128 cuts23954 = true := by
 decide +kernel
def pointBounds23954 : List (Nat × Nat × Nat) := [(3143695360,102349386345581,102349768053077)]
theorem point_links_checked23954 : (cuts23954.take 1).map (fun c => (3143630849-1+2*2^9*c.k,102349118897854+c.lower,102349500605202+c.upper)) = pointBounds23954 := by
 decide +kernel
def cuts23955 : List PrefixCut := [⟨31,124362681,124362752⟩,
⟨127,526540875,526541176⟩,
⟨128,531912717,531913021⟩]
theorem checked23955 : checkPrefixCuts (2^48) 3143761921 9 Manual.Count131072.C023955.packed 128 cuts23955 = true := by
 decide +kernel
def pointBounds23955 : List (Nat × Nat × Nat) := [(3143793664,102349785402754,102350167110478),(3143891968,102350187580948,102350569288902)]
theorem point_links_checked23955 : (cuts23955.take 2).map (fun c => (3143761921-1+2*2^9*c.k,102349661040073+c.lower,102350042747726+c.upper)) = pointBounds23955 := by
 decide +kernel
def cuts23956 : List PrefixCut := [⟨95,395450975,395451199⟩,
⟨128,534397548,534397849⟩]
theorem checked23956 : checkPrefixCuts (2^48) 3143892993 9 Manual.Count131072.C023956.packed 128 cuts23956 = true := by
 decide +kernel
def pointBounds23956 : List (Nat × Nat × Nat) := [(3143990272,102350588403765,102350970111946)]
theorem point_links_checked23956 : (cuts23956.take 1).map (fun c => (3143892993-1+2*2^9*c.k,102350192952790+c.lower,102350574660747+c.upper)) = pointBounds23956 := by
 decide +kernel
def cuts23957 : List PrefixCut := [⟨63,271532441,271532591⟩,
⟨128,543775448,543775746⟩]
theorem checked23957 : checkPrefixCuts (2^48) 3144024065 9 Manual.Count131072.C023957.packed 128 cuts23957 = true := by
 decide +kernel
def pointBounds23957 : List (Nat × Nat × Nat) := [(3144088576,102350998882779,102351380591187)]
theorem point_links_checked23957 : (cuts23957.take 1).map (fun c => (3144024065-1+2*2^9*c.k,102350727350338+c.lower,102351109058596+c.upper)) = pointBounds23957 := by
 decide +kernel
def cuts23958 : List PrefixCut := [⟨31,131598459,131598533⟩,
⟨127,535069314,535069623⟩,
⟨128,539724328,539724640⟩]
theorem checked23958 : checkPrefixCuts (2^48) 3144155137 9 Manual.Count131072.C023958.packed 128 cuts23958 = true := by
 decide +kernel
def pointBounds23958 : List (Nat × Nat × Nat) := [(3144186880,102351402724245,102351784432875),(3144285184,102351806195100,102352187903965)]
theorem point_links_checked23958 : (cuts23958.take 2).map (fun c => (3144155137-1+2*2^9*c.k,102351271125786+c.lower,102351652834342+c.upper)) = pointBounds23958 := by
 decide +kernel
def cuts23959 : List PrefixCut := [⟨95,403995205,403995428⟩,
⟨128,540417954,540418251⟩]
theorem checked23959 : checkPrefixCuts (2^48) 3144286209 9 Manual.Count131072.C023959.packed 128 cuts23959 = true := by
 decide +kernel
def pointBounds23959 : List (Nat × Nat × Nat) := [(3144383488,102352214845319,102352596554410)]
theorem point_links_checked23959 : (cuts23959.take 1).map (fun c => (3144286209-1+2*2^9*c.k,102351810850114+c.lower,102352192558982+c.upper)) = pointBounds23959 := by
 decide +kernel
def cuts23960 : List PrefixCut := [⟨63,261204322,261204474⟩,
⟨128,534397906,534398215⟩]
theorem checked23960 : checkPrefixCuts (2^48) 3144417281 9 Manual.Count131072.C023960.packed 128 cuts23960 = true := by
 decide +kernel
def pointBounds23960 : List (Nat × Nat × Nat) := [(3144481792,102352612472390,102352994181707)]
theorem point_links_checked23960 : (cuts23960.take 1).map (fun c => (3144417281-1+2*2^9*c.k,102352351268068+c.lower,102352732977233+c.upper)) = pointBounds23960 := by
 decide +kernel
def cuts23961 : List PrefixCut := [⟨31,130418360,130418433⟩,
⟨127,530795349,530795650⟩,
⟨128,535539290,535539593⟩]
theorem checked23961 : checkPrefixCuts (2^48) 3144548353 9 Manual.Count131072.C023961.packed 128 cuts23961 = true := by
 decide +kernel
def pointBounds23961 : List (Nat × Nat × Nat) := [(3144580096,102353016084334,102353397793881),(3144678400,102353416461323,102353798171098)]
theorem point_links_checked23961 : (cuts23961.take 2).map (fun c => (3144548353-1+2*2^9*c.k,102352885665974+c.lower,102353267375448+c.upper)) = pointBounds23961 := by
 decide +kernel
def cuts23962 : List PrefixCut := [⟨95,391950804,391951023⟩,
⟨128,531578678,531578973⟩]
theorem checked23962 : checkPrefixCuts (2^48) 3144679425 9 Manual.Count131072.C023962.packed 128 cuts23962 = true := by
 decide +kernel
def pointBounds23962 : List (Nat × Nat × Nat) := [(3144776704,102353813156068,102354194866064)]
theorem point_links_checked23962 : (cuts23962.take 1).map (fun c => (3144679425-1+2*2^9*c.k,102353421205264+c.lower,102353802915041+c.upper)) = pointBounds23962 := by
 decide +kernel
def cuts23963 : List PrefixCut := [⟨63,258755009,258755153⟩,
⟨128,531466907,531467205⟩]
theorem checked23963 : checkPrefixCuts (2^48) 3144810497 9 Manual.Count131072.C023963.packed 128 cuts23963 = true := by
 decide +kernel
def pointBounds23963 : List (Nat × Nat × Nat) := [(3144875008,102354211538951,102354593249167)]
theorem point_links_checked23963 : (cuts23963.take 1).map (fun c => (3144810497-1+2*2^9*c.k,102353952783942+c.lower,102354334494014+c.upper)) = pointBounds23963 := by
 decide +kernel
def cuts23964 : List PrefixCut := [⟨31,132550073,132550148⟩,
⟨127,530013048,530013347⟩,
⟨128,533861424,533861725⟩]
theorem checked23964 : checkPrefixCuts (2^48) 3144941569 9 Manual.Count131072.C023964.packed 128 cuts23964 = true := by
 decide +kernel
def pointBounds23964 : List (Nat × Nat × Nat) := [(3144973312,102354616800922,102354998511367),(3145071616,102355014263897,102355395974566)]
theorem point_links_checked23964 : (cuts23964.take 2).map (fun c => (3144941569-1+2*2^9*c.k,102354484250849+c.lower,102354865961219+c.upper)) = pointBounds23964 := by
 decide +kernel
def cuts23965 : List PrefixCut := [⟨95,400135288,400135514⟩,
⟨128,539298245,539298551⟩]
theorem checked23965 : checkPrefixCuts (2^48) 3145072641 9 Manual.Count131072.C023965.packed 128 cuts23965 = true := by
 decide +kernel
def pointBounds23965 : List (Nat × Nat × Nat) := [(3145169920,102355418247561,102355799958458)]
theorem point_links_checked23965 : (cuts23965.take 1).map (fun c => (3145072641-1+2*2^9*c.k,102355018112273+c.lower,102355399822944+c.upper)) = pointBounds23965 := by
 decide +kernel
def cuts23966 : List PrefixCut := [⟨63,264360735,264360882⟩,
⟨128,539096844,539097136⟩]
theorem checked23966 : checkPrefixCuts (2^48) 3145203713 9 Manual.Count131072.C023966.packed 128 cuts23966 = true := by
 decide +kernel
def pointBounds23966 : List (Nat × Nat × Nat) := [(3145268224,102355821771253,102356203482377)]
theorem point_links_checked23966 : (cuts23966.take 1).map (fun c => (3145203713-1+2*2^9*c.k,102355557410518+c.lower,102355939121495+c.upper)) = pointBounds23966 := by
 decide +kernel
def cuts23967 : List PrefixCut := [⟨31,131638607,131638679⟩,
⟨127,529230870,529231166⟩,
⟨128,533884139,533884437⟩]
theorem checked23967 : checkPrefixCuts (2^48) 3145334785 9 Manual.Count131072.C023967.packed 128 cuts23967 = true := by
 decide +kernel
def pointBounds23967 : List (Nat × Nat × Nat) := [(3145366528,102356228145969,102356609857310),(3145464832,102356625738232,102357007449797)]
theorem point_links_checked23967 : (cuts23967.take 2).map (fun c => (3145334785-1+2*2^9*c.k,102356096507362+c.lower,102356478218631+c.upper)) = pointBounds23967 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000123
