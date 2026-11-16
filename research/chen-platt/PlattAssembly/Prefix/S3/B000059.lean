import PlattAssemblyKernel
import PlattCertificates.Count131072.C021888
import PlattCertificates.Count131072.C021889
import PlattCertificates.Count131072.C021890
import PlattCertificates.Count131072.C021891
import PlattCertificates.Count131072.C021892
import PlattCertificates.Count131072.C021893
import PlattCertificates.Count131072.C021894
import PlattCertificates.Count131072.C021895
import PlattCertificates.Count131072.C021896
import PlattCertificates.Count131072.C021897
import PlattCertificates.Count131072.C021898
import PlattCertificates.Count131072.C021899
import PlattCertificates.Count131072.C021900
import PlattCertificates.Count131072.C021901
import PlattCertificates.Count131072.C021902
import PlattCertificates.Count131072.C021903
import PlattCertificates.Count131072.C021904
import PlattCertificates.Count131072.C021905
import PlattCertificates.Count131072.C021906
import PlattCertificates.Count131072.C021907
import PlattCertificates.Count131072.C021908
import PlattCertificates.Count131072.C021909
import PlattCertificates.Count131072.C021910
import PlattCertificates.Count131072.C021911
import PlattCertificates.Count131072.C021912
import PlattCertificates.Count131072.C021913
import PlattCertificates.Count131072.C021914
import PlattCertificates.Count131072.C021915
import PlattCertificates.Count131072.C021916
import PlattCertificates.Count131072.C021917
import PlattCertificates.Count131072.C021918
import PlattCertificates.Count131072.C021919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21888 : List PrefixCut := [⟨82,378973594,378973811⟩,
⟨128,586385356,586385695⟩]
theorem checked21888 : checkPrefixCuts (2^48) 2872836097 9 Manual.Count131072.C021888.packed 128 cuts21888 = true := by
 decide +kernel
def pointBounds21888 : List (Nat × Nat × Nat) := [(2872920064,101187814969486,101188196016295)]
theorem point_links_checked21888 : (cuts21888.take 1).map (fun c => (2872836097-1+2*2^9*c.k,101187435995892+c.lower,101187817042484+c.upper)) = pointBounds21888 := by
 decide +kernel
def cuts21889 : List PrefixCut := [⟨42,196239622,196239734⟩,
⟨128,585280914,585281249⟩]
theorem checked21889 : checkPrefixCuts (2^48) 2872967169 9 Manual.Count131072.C021889.packed 128 cuts21889 = true := by
 decide +kernel
def pointBounds21889 : List (Nat × Nat × Nat) := [(2873010176,101188218620870,101188599667913)]
theorem point_links_checked21889 : (cuts21889.take 1).map (fun c => (2872967169-1+2*2^9*c.k,101188022381248+c.lower,101188403428179+c.upper)) = pointBounds21889 := by
 decide +kernel
def cuts21890 : List PrefixCut := [⟨2,10090816,10090821⟩,
⟨90,411561621,411561856⟩,
⟨128,584666341,584666673⟩]
theorem checked21890 : checkPrefixCuts (2^48) 2873098241 9 Manual.Count131072.C021890.packed 128 cuts21890 = true := by
 decide +kernel
def pointBounds21890 : List (Nat × Nat × Nat) := [(2873100288,101188617752978,101188998800249),(2873190400,101189019223783,101189400271284)]
theorem point_links_checked21890 : (cuts21890.take 2).map (fun c => (2873098241-1+2*2^9*c.k,101188607662162+c.lower,101188988709428+c.upper)) = pointBounds21890 := by
 decide +kernel
def cuts21891 : List PrefixCut := [⟨50,228549526,228549654⟩,
⟨128,583660109,583660437⟩]
theorem checked21891 : checkPrefixCuts (2^48) 2873229313 9 Manual.Count131072.C021891.packed 128 cuts21891 = true := by
 decide +kernel
def pointBounds21891 : List (Nat × Nat × Nat) := [(2873280512,101189420878029,101189801925755)]
theorem point_links_checked21891 : (cuts21891.take 1).map (fun c => (2873229313-1+2*2^9*c.k,101189192328503+c.lower,101189573376101+c.upper)) = pointBounds21891 := by
 decide +kernel
def cuts21892 : List PrefixCut := [⟨10,45257521,45257545⟩,
⟨98,446494652,446494909⟩,
⟨128,586865936,586866272⟩]
theorem checked21892 : checkPrefixCuts (2^48) 2873360385 9 Manual.Count131072.C021892.packed 128 cuts21892 = true := by
 decide +kernel
def pointBounds21892 : List (Nat × Nat × Nat) := [(2873370624,101189821246133,101190202294083),(2873460736,101190222483264,101190603531447)]
theorem point_links_checked21892 : (cuts21892.take 2).map (fun c => (2873360385-1+2*2^9*c.k,101189775988612+c.lower,101190157036538+c.upper)) = pointBounds21892 := by
 decide +kernel
def cuts21893 : List PrefixCut := [⟨58,269963129,269963276⟩,
⟨128,594381688,594382017⟩]
theorem checked21893 : checkPrefixCuts (2^48) 2873491457 9 Manual.Count131072.C021893.packed 128 cuts21893 = true := by
 decide +kernel
def pointBounds21893 : List (Nat × Nat × Nat) := [(2873550848,101190632817677,101191013866086)]
theorem point_links_checked21893 : (cuts21893.take 1).map (fun c => (2873491457-1+2*2^9*c.k,101190362854548+c.lower,101190743902810+c.upper)) = pointBounds21893 := by
 decide +kernel
def cuts21894 : List PrefixCut := [⟨18,81005420,81005465⟩,
⟨106,478972557,478972835⟩,
⟨128,584853430,584853768⟩]
theorem checked21894 : checkPrefixCuts (2^48) 2873622529 9 Manual.Count131072.C021894.packed 128 cuts21894 = true := by
 decide +kernel
def pointBounds21894 : List (Nat × Nat × Nat) := [(2873640960,101191038241656,101191419290292),(2873731072,101191436208793,101191817257662)]
theorem point_links_checked21894 : (cuts21894.take 2).map (fun c => (2873622529-1+2*2^9*c.k,101190957236236+c.lower,101191338284827+c.upper)) = pointBounds21894 := by
 decide +kernel
def cuts21895 : List PrefixCut := [⟨66,309214315,309214488⟩,
⟨128,602162993,602163330⟩]
theorem checked21895 : checkPrefixCuts (2^48) 2873753601 9 Manual.Count131072.C021895.packed 128 cuts21895 = true := by
 decide +kernel
def pointBounds21895 : List (Nat × Nat × Nat) := [(2873821184,101191851303981,101192232353083)]
theorem point_links_checked21895 : (cuts21895.take 1).map (fun c => (2873753601-1+2*2^9*c.k,101191542089666+c.lower,101191923138595+c.upper)) = pointBounds21895 := by
 decide +kernel
def cuts21896 : List PrefixCut := [⟨26,122329368,122329437⟩,
⟨114,527408651,527408953⟩,
⟨128,596650878,596651217⟩]
theorem checked21896 : checkPrefixCuts (2^48) 2873884673 9 Manual.Count131072.C021896.packed 128 cuts21896 = true := by
 decide +kernel
def pointBounds21896 : List (Nat × Nat × Nat) := [(2873911296,101192266582027,101192647631362),(2874001408,101192671661310,101193052710878)]
theorem point_links_checked21896 : (cuts21896.take 2).map (fun c => (2873884673-1+2*2^9*c.k,101192144252659+c.lower,101192525301925+c.upper)) = pointBounds21896 := by
 decide +kernel
def cuts21897 : List PrefixCut := [⟨74,349241726,349241921⟩,
⟨128,598092831,598093161⟩]
theorem checked21897 : checkPrefixCuts (2^48) 2874015745 9 Manual.Count131072.C021897.packed 128 cuts21897 = true := by
 decide +kernel
def pointBounds21897 : List (Nat × Nat × Nat) := [(2874091520,101193090145263,101193471195063)]
theorem point_links_checked21897 : (cuts21897.take 1).map (fun c => (2874015745-1+2*2^9*c.k,101192740903537+c.lower,101193121953142+c.upper)) = pointBounds21897 := by
 decide +kernel
def cuts21898 : List PrefixCut := [⟨34,156006921,156007012⟩,
⟨122,561733622,561733941⟩,
⟨128,588272385,588272719⟩]
theorem checked21898 : checkPrefixCuts (2^48) 2874146817 9 Manual.Count131072.C021898.packed 128 cuts21898 = true := by
 decide +kernel
def pointBounds21898 : List (Nat × Nat × Nat) := [(2874181632,101193495003289,101193876053315),(2874271744,101193900729990,101194281780244)]
theorem point_links_checked21898 : (cuts21898.take 2).map (fun c => (2874146817-1+2*2^9*c.k,101193338996368+c.lower,101193720046303+c.upper)) = pointBounds21898 := by
 decide +kernel
def cuts21899 : List PrefixCut := [⟨82,376628983,376629200⟩,
⟨128,588930919,588931259⟩]
theorem checked21899 : checkPrefixCuts (2^48) 2874277889 9 Manual.Count131072.C021899.packed 128 cuts21899 = true := by
 decide +kernel
def pointBounds21899 : List (Nat × Nat × Nat) := [(2874361856,101194303897736,101194684948222)]
theorem point_links_checked21899 : (cuts21899.take 1).map (fun c => (2874277889-1+2*2^9*c.k,101193927268753+c.lower,101194308319022+c.upper)) = pointBounds21899 := by
 decide +kernel
def cuts21900 : List PrefixCut := [⟨42,189874061,189874172⟩,
⟨128,584987229,584987566⟩]
theorem checked21900 : checkPrefixCuts (2^48) 2874408961 9 Manual.Count131072.C021900.packed 128 cuts21900 = true := by
 decide +kernel
def pointBounds21900 : List (Nat × Nat × Nat) := [(2874451968,101194706073733,101195087124453)]
theorem point_links_checked21900 : (cuts21900.take 1).map (fun c => (2874408961-1+2*2^9*c.k,101194516199672+c.lower,101194897250281+c.upper)) = pointBounds21900 := by
 decide +kernel
def cuts21901 : List PrefixCut := [⟨2,8812795,8812800⟩,
⟨90,412726056,412726296⟩,
⟨128,589268902,589269245⟩]
theorem checked21901 : checkPrefixCuts (2^48) 2874540033 9 Manual.Count131072.C021901.packed 128 cuts21901 = true := by
 decide +kernel
def pointBounds21901 : List (Nat × Nat × Nat) := [(2874542080,101195109999696,101195491050647),(2874632192,101195513912957,101195894964143)]
theorem point_links_checked21901 : (cuts21901.take 2).map (fun c => (2874540033-1+2*2^9*c.k,101195101186901+c.lower,101195482237847+c.upper)) = pointBounds21901 := by
 decide +kernel
def cuts21902 : List PrefixCut := [⟨50,234701420,234701551⟩,
⟨128,590319313,590319647⟩]
theorem checked21902 : checkPrefixCuts (2^48) 2874671105 9 Manual.Count131072.C021902.packed 128 cuts21902 = true := by
 decide +kernel
def pointBounds21902 : List (Nat × Nat × Nat) := [(2874722304,101195925157223,101196306208643)]
theorem point_links_checked21902 : (cuts21902.take 1).map (fun c => (2874671105-1+2*2^9*c.k,101195690455803+c.lower,101196071507092+c.upper)) = pointBounds21902 := by
 decide +kernel
def cuts21903 : List PrefixCut := [⟨10,43668248,43668274⟩,
⟨98,449697604,449697862⟩,
⟨128,589215229,589215567⟩]
theorem checked21903 : checkPrefixCuts (2^48) 2874802177 9 Manual.Count131072.C021903.packed 128 cuts21903 = true := by
 decide +kernel
def pointBounds21903 : List (Nat × Nat × Nat) := [(2874812416,101196324443364,101196705495013),(2874902528,101196730472720,101197111524601)]
theorem point_links_checked21903 : (cuts21903.take 2).map (fun c => (2874802177-1+2*2^9*c.k,101196280775116+c.lower,101196661826739+c.upper)) = pointBounds21903 := by
 decide +kernel
def cuts21904 : List PrefixCut := [⟨58,261212029,261212178⟩,
⟨128,577733527,577733862⟩]
theorem checked21904 : checkPrefixCuts (2^48) 2874933249 9 Manual.Count131072.C021904.packed 128 cuts21904 = true := by
 decide +kernel
def pointBounds21904 : List (Nat × Nat × Nat) := [(2874992640,101197131202374,101197512254484)]
theorem point_links_checked21904 : (cuts21904.take 1).map (fun c => (2874933249-1+2*2^9*c.k,101196869990345+c.lower,101197251042306+c.upper)) = pointBounds21904 := by
 decide +kernel
def cuts21905 : List PrefixCut := [⟨18,84685058,84685109⟩,
⟨106,490871988,490872271⟩,
⟨128,592490157,592490495⟩]
theorem checked21905 : checkPrefixCuts (2^48) 2875064321 9 Manual.Count131072.C021905.packed 128 cuts21905 = true := by
 decide +kernel
def pointBounds21905 : List (Nat × Nat × Nat) := [(2875082752,101197532408930,101197913461277),(2875172864,101197938595860,101198319648439)]
theorem point_links_checked21905 : (cuts21905.take 2).map (fun c => (2875064321-1+2*2^9*c.k,101197447723872+c.lower,101197828776168+c.upper)) = pointBounds21905 := by
 decide +kernel
def cuts21906 : List PrefixCut := [⟨66,310723532,310723708⟩,
⟨128,602546336,602546681⟩]
theorem checked21906 : checkPrefixCuts (2^48) 2875195393 9 Manual.Count131072.C021906.packed 128 cuts21906 = true := by
 decide +kernel
def pointBounds21906 : List (Nat × Nat × Nat) := [(2875262976,101198350937561,101198731990371)]
theorem point_links_checked21906 : (cuts21906.take 1).map (fun c => (2875195393-1+2*2^9*c.k,101198040214029+c.lower,101198421266663+c.upper)) = pointBounds21906 := by
 decide +kernel
def cuts21907 : List PrefixCut := [⟨26,117079723,117079793⟩,
⟨114,515984538,515984839⟩,
⟨128,578633485,578633819⟩]
theorem checked21907 : checkPrefixCuts (2^48) 2875326465 9 Manual.Count131072.C021907.packed 128 cuts21907 = true := by
 decide +kernel
def pointBounds21907 : List (Nat × Nat × Nat) := [(2875353088,101198759840088,101199140893137),(2875443200,101199158744903,101199539798183)]
theorem point_links_checked21907 : (cuts21907.take 2).map (fun c => (2875326465-1+2*2^9*c.k,101198642760365+c.lower,101199023813344+c.upper)) = pointBounds21907 := by
 decide +kernel
def cuts21908 : List PrefixCut := [⟨74,335264508,335264703⟩,
⟨128,581152164,581152497⟩]
theorem checked21908 : checkPrefixCuts (2^48) 2875457537 9 Manual.Count131072.C021908.packed 128 cuts21908 = true := by
 decide +kernel
def pointBounds21908 : List (Nat × Nat × Nat) := [(2875533312,101199556658358,101199937711866)]
theorem point_links_checked21908 : (cuts21908.take 1).map (fun c => (2875457537-1+2*2^9*c.k,101199221393850+c.lower,101199602447163+c.upper)) = pointBounds21908 := by
 decide +kernel
def cuts21909 : List PrefixCut := [⟨34,156613875,156613961⟩,
⟨122,562724406,562724719⟩,
⟨128,591794741,591795070⟩]
theorem checked21909 : checkPrefixCuts (2^48) 2875588609 9 Manual.Count131072.C021909.packed 128 cuts21909 = true := by
 decide +kernel
def pointBounds21909 : List (Nat × Nat × Nat) := [(2875623424,101199959159889,101200340213621),(2875713536,101200365270420,101200746324379)]
theorem point_links_checked21909 : (cuts21909.take 2).map (fun c => (2875588609-1+2*2^9*c.k,101199802546014+c.lower,101200183599660+c.upper)) = pointBounds21909 := by
 decide +kernel
def cuts21910 : List PrefixCut := [⟨82,377712634,377712849⟩,
⟨128,588146380,588146718⟩]
theorem checked21910 : checkPrefixCuts (2^48) 2875719681 9 Manual.Count131072.C021910.packed 128 cuts21910 = true := by
 decide +kernel
def pointBounds21910 : List (Nat × Nat × Nat) := [(2875803648,101200772053389,101201153107579)]
theorem point_links_checked21910 : (cuts21910.take 1).map (fun c => (2875719681-1+2*2^9*c.k,101200394340755+c.lower,101200775394730+c.upper)) = pointBounds21910 := by
 decide +kernel
def cuts21911 : List PrefixCut := [⟨42,194476855,194476966⟩,
⟨128,591251646,591251991⟩]
theorem checked21911 : checkPrefixCuts (2^48) 2875850753 9 Manual.Count131072.C021911.packed 128 cuts21911 = true := by
 decide +kernel
def pointBounds21911 : List (Nat × Nat × Nat) := [(2875893760,101201176963990,101201558018414)]
theorem point_links_checked21911 : (cuts21911.take 1).map (fun c => (2875850753-1+2*2^9*c.k,101200982487135+c.lower,101201363541448+c.upper)) = pointBounds21911 := by
 decide +kernel
def cuts21912 : List PrefixCut := [⟨2,9493473,9493478⟩,
⟨90,411638303,411638543⟩,
⟨128,583884403,583884740⟩]
theorem checked21912 : checkPrefixCuts (2^48) 2875981825 9 Manual.Count131072.C021912.packed 128 cuts21912 = true := by
 decide +kernel
def pointBounds21912 : List (Nat × Nat × Nat) := [(2875983872,101201583232254,101201964286917),(2876073984,101201985377084,101202366431982)]
theorem point_links_checked21912 : (cuts21912.take 2).map (fun c => (2875981825-1+2*2^9*c.k,101201573738781+c.lower,101201954793439+c.upper)) = pointBounds21912 := by
 decide +kernel
def cuts21913 : List PrefixCut := [⟨50,227439525,227439655⟩,
⟨128,586793669,586794003⟩]
theorem checked21913 : checkPrefixCuts (2^48) 2876112897 9 Manual.Count131072.C021913.packed 128 cuts21913 = true := by
 decide +kernel
def pointBounds21913 : List (Nat × Nat × Nat) := [(2876164096,101202385062709,101202766117834)]
theorem point_links_checked21913 : (cuts21913.take 1).map (fun c => (2876112897-1+2*2^9*c.k,101202157623184+c.lower,101202538678179+c.upper)) = pointBounds21913 := by
 decide +kernel
def cuts21914 : List PrefixCut := [⟨10,44820701,44820728⟩,
⟨98,457594567,457594830⟩,
⟨128,598118699,598119042⟩]
theorem checked21914 : checkPrefixCuts (2^48) 2876243969 9 Manual.Count131072.C021914.packed 128 cuts21914 = true := by
 decide +kernel
def pointBounds21914 : List (Nat × Nat × Nat) := [(2876254208,101202789237554,101203170292910),(2876344320,101203202011420,101203583067012)]
theorem point_links_checked21914 : (cuts21914.take 2).map (fun c => (2876243969-1+2*2^9*c.k,101202744416853+c.lower,101203125472182+c.upper)) = pointBounds21914 := by
 decide +kernel
def cuts21915 : List PrefixCut := [⟨58,265386832,265386980⟩,
⟨128,585566016,585566339⟩]
theorem checked21915 : checkPrefixCuts (2^48) 2876375041 9 Manual.Count131072.C021915.packed 128 cuts21915 = true := by
 decide +kernel
def pointBounds21915 : List (Nat × Nat × Nat) := [(2876434432,101203607922384,101203988978204)]
theorem point_links_checked21915 : (cuts21915.take 1).map (fun c => (2876375041-1+2*2^9*c.k,101203342535552+c.lower,101203723591224+c.upper)) = pointBounds21915 := by
 decide +kernel
def cuts21916 : List PrefixCut := [⟨18,81609182,81609229⟩,
⟨106,489940969,489941252⟩,
⟨128,589649064,589649403⟩]
theorem checked21916 : checkPrefixCuts (2^48) 2876506113 9 Manual.Count131072.C021916.packed 128 cuts21916 = true := by
 decide +kernel
def pointBounds21916 : List (Nat × Nat × Nat) := [(2876524544,101204009710750,101204390766792),(2876614656,101204418042537,101204799098815)]
theorem point_links_checked21916 : (cuts21916.take 2).map (fun c => (2876506113-1+2*2^9*c.k,101203928101568+c.lower,101204309157563+c.upper)) = pointBounds21916 := by
 decide +kernel
def cuts21917 : List PrefixCut := [⟨66,301076552,301076722⟩,
⟨128,581794485,581794821⟩]
theorem checked21917 : checkPrefixCuts (2^48) 2876637185 9 Manual.Count131072.C021917.packed 128 cuts21917 = true := by
 decide +kernel
def pointBounds21917 : List (Nat × Nat × Nat) := [(2876704768,101204818827184,101205199883688)]
theorem point_links_checked21917 : (cuts21917.take 1).map (fun c => (2876637185-1+2*2^9*c.k,101204517750632+c.lower,101204898806966+c.upper)) = pointBounds21917 := by
 decide +kernel
def cuts21918 : List PrefixCut := [⟨26,119467128,119467197⟩,
⟨114,525510219,525510505⟩,
⟨128,593117604,593117930⟩]
theorem checked21918 : checkPrefixCuts (2^48) 2876768257 9 Manual.Count131072.C021918.packed 128 cuts21918 = true := by
 decide +kernel
def pointBounds21918 : List (Nat × Nat × Nat) := [(2876794880,101205219012245,101205600068984),(2876884992,101205625055336,101206006112292)]
theorem point_links_checked21918 : (cuts21918.take 2).map (fun c => (2876768257-1+2*2^9*c.k,101205099545117+c.lower,101205480601787+c.upper)) = pointBounds21918 := by
 decide +kernel
def cuts21919 : List PrefixCut := [⟨74,340281951,340282144⟩,
⟨128,589764160,589764496⟩]
theorem checked21919 : checkPrefixCuts (2^48) 2876899329 9 Manual.Count131072.C021919.packed 128 cuts21919 = true := by
 decide +kernel
def pointBounds21919 : List (Nat × Nat × Nat) := [(2876975104,101206032944672,101206414001861)]
theorem point_links_checked21919 : (cuts21919.take 1).map (fun c => (2876899329-1+2*2^9*c.k,101205692662721+c.lower,101206073719717+c.upper)) = pointBounds21919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000059
