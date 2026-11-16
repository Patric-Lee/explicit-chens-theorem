import PlattAssemblyKernel
import PlattCertificates.Count131072.C028928
import PlattCertificates.Count131072.C028929
import PlattCertificates.Count131072.C028930
import PlattCertificates.Count131072.C028931
import PlattCertificates.Count131072.C028932
import PlattCertificates.Count131072.C028933
import PlattCertificates.Count131072.C028934
import PlattCertificates.Count131072.C028935
import PlattCertificates.Count131072.C028936
import PlattCertificates.Count131072.C028937
import PlattCertificates.Count131072.C028938
import PlattCertificates.Count131072.C028939
import PlattCertificates.Count131072.C028940
import PlattCertificates.Count131072.C028941
import PlattCertificates.Count131072.C028942
import PlattCertificates.Count131072.C028943
import PlattCertificates.Count131072.C028944
import PlattCertificates.Count131072.C028945
import PlattCertificates.Count131072.C028946
import PlattCertificates.Count131072.C028947
import PlattCertificates.Count131072.C028948
import PlattCertificates.Count131072.C028949
import PlattCertificates.Count131072.C028950
import PlattCertificates.Count131072.C028951
import PlattCertificates.Count131072.C028952
import PlattCertificates.Count131072.C028953
import PlattCertificates.Count131072.C028954
import PlattCertificates.Count131072.C028955
import PlattCertificates.Count131072.C028956
import PlattCertificates.Count131072.C028957
import PlattCertificates.Count131072.C028958
import PlattCertificates.Count131072.C028959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28928 : List PrefixCut := [⟨47,161961244,161961331⟩,
⟨128,443757069,443757308⟩]
theorem checked28928 : checkPrefixCuts (2^48) 3795582977 9 Manual.Count131072.C028928.packed 128 cuts28928 = true := by
 decide +kernel
def pointBounds28928 : List (Nat × Nat × Nat) := [(3795631104,104764696251398,104765079312834)]
theorem point_links_checked28928 : (cuts28928.take 1).map (fun c => (3795582977-1+2*2^9*c.k,104764534290154+c.lower,104764917351503+c.upper)) = pointBounds28928 := by
 decide +kernel
def cuts28929 : List PrefixCut := [⟨35,119613039,119613107⟩,
⟨128,439069974,439070223⟩]
theorem checked28929 : checkPrefixCuts (2^48) 3795714049 9 Manual.Count131072.C028929.packed 128 cuts28929 = true := by
 decide +kernel
def pointBounds28929 : List (Nat × Nat × Nat) := [(3795749888,104765097660262,104765480721918)]
theorem point_links_checked28929 : (cuts28929.take 1).map (fun c => (3795714049-1+2*2^9*c.k,104764978047223+c.lower,104765361108811+c.upper)) = pointBounds28929 := by
 decide +kernel
def cuts28930 : List PrefixCut := [⟨23,80233758,80233803⟩,
⟨128,446840825,446841077⟩]
theorem checked28930 : checkPrefixCuts (2^48) 3795845121 9 Manual.Count131072.C028930.packed 128 cuts28930 = true := by
 decide +kernel
def pointBounds28930 : List (Nat × Nat × Nat) := [(3795868672,104765497350955,104765880412837)]
theorem point_links_checked28930 : (cuts28930.take 1).map (fun c => (3795845121-1+2*2^9*c.k,104765417117197+c.lower,104765800179034+c.upper)) = pointBounds28930 := by
 decide +kernel
def cuts28931 : List PrefixCut := [⟨11,38854992,38855012⟩,
⟨127,438743107,438743351⟩,
⟨128,442450523,442450769⟩]
theorem checked28931 : checkPrefixCuts (2^48) 3795976193 9 Manual.Count131072.C028931.packed 128 cuts28931 = true := by
 decide +kernel
def pointBounds28931 : List (Nat × Nat × Nat) := [(3795987456,104765902813014,104766285875123),(3796106240,104766302701129,104766685763462)]
theorem point_links_checked28931 : (cuts28931.take 2).map (fun c => (3795976193-1+2*2^9*c.k,104765863958022+c.lower,104766247020111+c.upper)) = pointBounds28931 := by
 decide +kernel
def cuts28932 : List PrefixCut := [⟨115,396242375,396242590⟩,
⟨128,443399148,443399388⟩]
theorem checked28932 : checkPrefixCuts (2^48) 3796107265 9 Manual.Count131072.C028932.packed 128 cuts28932 = true := by
 decide +kernel
def pointBounds28932 : List (Nat × Nat × Nat) := [(3796225024,104766702650920,104767085713470)]
theorem point_links_checked28932 : (cuts28932.take 1).map (fun c => (3796107265-1+2*2^9*c.k,104766306408545+c.lower,104766689470880+c.upper)) = pointBounds28932 := by
 decide +kernel
def cuts28933 : List PrefixCut := [⟨103,355894610,355894812⟩,
⟨128,443013138,443013389⟩]
theorem checked28933 : checkPrefixCuts (2^48) 3796238337 9 Manual.Count131072.C028933.packed 128 cuts28933 = true := by
 decide +kernel
def pointBounds28933 : List (Nat × Nat × Nat) := [(3796343808,104767105702303,104767488765080)]
theorem point_links_checked28933 : (cuts28933.take 1).map (fun c => (3796238337-1+2*2^9*c.k,104766749807693+c.lower,104767132870268+c.upper)) = pointBounds28933 := by
 decide +kernel
def cuts28934 : List PrefixCut := [⟨91,314511496,314511670⟩,
⟨128,437956254,437956499⟩]
theorem checked28934 : checkPrefixCuts (2^48) 3796369409 9 Manual.Count131072.C028934.packed 128 cuts28934 = true := by
 decide +kernel
def pointBounds28934 : List (Nat × Nat × Nat) := [(3796462592,104767507332327,104767890395327)]
theorem point_links_checked28934 : (cuts28934.take 1).map (fun c => (3796369409-1+2*2^9*c.k,104767192820831+c.lower,104767575883657+c.upper)) = pointBounds28934 := by
 decide +kernel
def cuts28935 : List PrefixCut := [⟨79,273057014,273057168⟩,
⟨128,440906695,440906944⟩]
theorem checked28935 : checkPrefixCuts (2^48) 3796500481 9 Manual.Count131072.C028935.packed 128 cuts28935 = true := by
 decide +kernel
def pointBounds28935 : List (Nat × Nat × Nat) := [(3796581376,104767903834099,104768286897324)]
theorem point_links_checked28935 : (cuts28935.take 1).map (fun c => (3796500481-1+2*2^9*c.k,104767630777085+c.lower,104768013840156+c.upper)) = pointBounds28935 := by
 decide +kernel
def cuts28936 : List PrefixCut := [⟨67,229974201,229974330⟩,
⟨128,441484543,441484792⟩]
theorem checked28936 : checkPrefixCuts (2^48) 3796631553 9 Manual.Count131072.C028936.packed 128 cuts28936 = true := by
 decide +kernel
def pointBounds28936 : List (Nat × Nat × Nat) := [(3796700160,104768301657981,104768684721430)]
theorem point_links_checked28936 : (cuts28936.take 1).map (fun c => (3796631553-1+2*2^9*c.k,104768071683780+c.lower,104768454747100+c.upper)) = pointBounds28936 := by
 decide +kernel
def cuts28937 : List PrefixCut := [⟨55,190971618,190971725⟩,
⟨128,448067195,448067445⟩]
theorem checked28937 : checkPrefixCuts (2^48) 3796762625 9 Manual.Count131072.C028937.packed 128 cuts28937 = true := by
 decide +kernel
def pointBounds28937 : List (Nat × Nat × Nat) := [(3796818944,104768704139941,104769087203617)]
theorem point_links_checked28937 : (cuts28937.take 1).map (fun c => (3796762625-1+2*2^9*c.k,104768513168323+c.lower,104768896231892+c.upper)) = pointBounds28937 := by
 decide +kernel
def cuts28938 : List PrefixCut := [⟨43,146041047,146041130⟩,
⟨128,436487219,436487465⟩]
theorem checked28938 : checkPrefixCuts (2^48) 3796893697 9 Manual.Count131072.C028938.packed 128 cuts28938 = true := by
 decide +kernel
def pointBounds28938 : List (Nat × Nat × Nat) := [(3796937728,104769107276565,104769490340467)]
theorem point_links_checked28938 : (cuts28938.take 1).map (fun c => (3796893697-1+2*2^9*c.k,104768961235518+c.lower,104769344299337+c.upper)) = pointBounds28938 := by
 decide +kernel
def cuts28939 : List PrefixCut := [⟨31,103485587,103485646⟩,
⟨128,438844219,438844464⟩]
theorem checked28939 : checkPrefixCuts (2^48) 3797024769 9 Manual.Count131072.C028939.packed 128 cuts28939 = true := by
 decide +kernel
def pointBounds28939 : List (Nat × Nat × Nat) := [(3797056512,104769501208324,104769884272448)]
theorem point_links_checked28939 : (cuts28939.take 1).map (fun c => (3797024769-1+2*2^9*c.k,104769397722737+c.lower,104769780786802+c.upper)) = pointBounds28939 := by
 decide +kernel
def cuts28940 : List PrefixCut := [⟨19,67011376,67011414⟩,
⟨128,447279577,447279825⟩]
theorem checked28940 : checkPrefixCuts (2^48) 3797155841 9 Manual.Count131072.C028940.packed 128 cuts28940 = true := by
 decide +kernel
def pointBounds28940 : List (Nat × Nat × Nat) := [(3797175296,104769903578332,104770286642680)]
theorem point_links_checked28940 : (cuts28940.take 1).map (fun c => (3797155841-1+2*2^9*c.k,104769836566956+c.lower,104770219631266+c.upper)) = pointBounds28940 := by
 decide +kernel
def cuts28941 : List PrefixCut := [⟨7,23645936,23645951⟩,
⟨123,420283302,420283539⟩,
⟨128,437850394,437850641⟩]
theorem checked28941 : checkPrefixCuts (2^48) 3797286913 9 Manual.Count131072.C028941.packed 128 cuts28941 = true := by
 decide +kernel
def pointBounds28941 : List (Nat × Nat × Nat) := [(3797294080,104770307492469,104770690557042),(3797412864,104770704129835,104771087194630)]
theorem point_links_checked28941 : (cuts28941.take 2).map (fun c => (3797286913-1+2*2^9*c.k,104770283846533+c.lower,104770666911091+c.upper)) = pointBounds28941 := by
 decide +kernel
def cuts28942 : List PrefixCut := [⟨111,376241230,376241439⟩,
⟨128,434944522,434944764⟩]
theorem checked28942 : checkPrefixCuts (2^48) 3797417985 9 Manual.Count131072.C028942.packed 128 cuts28942 = true := by
 decide +kernel
def pointBounds28942 : List (Nat × Nat × Nat) := [(3797531648,104771097938157,104771481003171)]
theorem point_links_checked28942 : (cuts28942.take 1).map (fun c => (3797417985-1+2*2^9*c.k,104770721696927+c.lower,104771104761732+c.upper)) = pointBounds28942 := by
 decide +kernel
def cuts28943 : List PrefixCut := [⟨99,337019828,337020019⟩,
⟨128,435670722,435670964⟩]
theorem checked28943 : checkPrefixCuts (2^48) 3797549057 9 Manual.Count131072.C028943.packed 128 cuts28943 = true := by
 decide +kernel
def pointBounds28943 : List (Nat × Nat × Nat) := [(3797650432,104771493661277,104771876726515)]
theorem point_links_checked28943 : (cuts28943.take 1).map (fun c => (3797549057-1+2*2^9*c.k,104771156641449+c.lower,104771539706496+c.upper)) = pointBounds28943 := by
 decide +kernel
def cuts28944 : List PrefixCut := [⟨87,297578664,297578834⟩,
⟨128,440028540,440028790⟩]
theorem checked28944 : checkPrefixCuts (2^48) 3797680129 9 Manual.Count131072.C028944.packed 128 cuts28944 = true := by
 decide +kernel
def pointBounds28944 : List (Nat × Nat × Nat) := [(3797769216,104771889890835,104772272956294)]
theorem point_links_checked28944 : (cuts28944.take 1).map (fun c => (3797680129-1+2*2^9*c.k,104771592312171+c.lower,104771975377460+c.upper)) = pointBounds28944 := by
 decide +kernel
def cuts28945 : List PrefixCut := [⟨75,263253914,263254062⟩,
⟨128,444830760,444831008⟩]
theorem checked28945 : checkPrefixCuts (2^48) 3797811201 9 Manual.Count131072.C028945.packed 128 cuts28945 = true := by
 decide +kernel
def pointBounds28945 : List (Nat × Nat × Nat) := [(3797888000,104772295594625,104772678660312)]
theorem point_links_checked28945 : (cuts28945.take 1).map (fun c => (3797811201-1+2*2^9*c.k,104772032340711+c.lower,104772415406250+c.upper)) = pointBounds28945 := by
 decide +kernel
def cuts28946 : List PrefixCut := [⟨63,217221816,217221942⟩,
⟨128,441999164,441999417⟩]
theorem checked28946 : checkPrefixCuts (2^48) 3797942273 9 Manual.Count131072.C028946.packed 128 cuts28946 = true := by
 decide +kernel
def pointBounds28946 : List (Nat × Nat × Nat) := [(3798006784,104772694393287,104773077459200)]
theorem point_links_checked28946 : (cuts28946.take 1).map (fun c => (3797942273-1+2*2^9*c.k,104772477171471+c.lower,104772860237258+c.upper)) = pointBounds28946 := by
 decide +kernel
def cuts28947 : List PrefixCut := [⟨51,174527648,174527744⟩,
⟨128,439390089,439390336⟩]
theorem checked28947 : checkPrefixCuts (2^48) 3798073345 9 Manual.Count131072.C028947.packed 128 cuts28947 = true := by
 decide +kernel
def pointBounds28947 : List (Nat × Nat × Nat) := [(3798125568,104773093698283,104773476764419)]
theorem point_links_checked28947 : (cuts28947.take 1).map (fun c => (3798073345-1+2*2^9*c.k,104772919170635+c.lower,104773302236675+c.upper)) = pointBounds28947 := by
 decide +kernel
def cuts28948 : List PrefixCut := [⟨39,135393436,135393513⟩,
⟨128,443821304,443821550⟩]
theorem checked28948 : checkPrefixCuts (2^48) 3798204417 9 Manual.Count131072.C028948.packed 128 cuts28948 = true := by
 decide +kernel
def pointBounds28948 : List (Nat × Nat × Nat) := [(3798244352,104773493954160,104773877020524)]
theorem point_links_checked28948 : (cuts28948.take 1).map (fun c => (3798204417-1+2*2^9*c.k,104773358560724+c.lower,104773741627011+c.upper)) = pointBounds28948 := by
 decide +kernel
def cuts28949 : List PrefixCut := [⟨27,91815515,91815566⟩,
⟨128,438470515,438470758⟩]
theorem checked28949 : checkPrefixCuts (2^48) 3798335489 9 Manual.Count131072.C028949.packed 128 cuts28949 = true := by
 decide +kernel
def pointBounds28949 : List (Nat × Nat × Nat) := [(3798363136,104773894197543,104774277264127)]
theorem point_links_checked28949 : (cuts28949.take 1).map (fun c => (3798335489-1+2*2^9*c.k,104773802382028+c.lower,104774185448561+c.upper)) = pointBounds28949 := by
 decide +kernel
def cuts28950 : List PrefixCut := [⟨15,52019669,52019699⟩,
⟨128,438381276,438381519⟩]
theorem checked28950 : checkPrefixCuts (2^48) 3798466561 9 Manual.Count131072.C028950.packed 128 cuts28950 = true := by
 decide +kernel
def pointBounds28950 : List (Nat × Nat × Nat) := [(3798481920,104774292872212,104774675939018)]
theorem point_links_checked28950 : (cuts28950.take 1).map (fun c => (3798466561-1+2*2^9*c.k,104774240852543+c.lower,104774623919319+c.upper)) = pointBounds28950 := by
 decide +kernel
def cuts28951 : List PrefixCut := [⟨3,9707055,9707061⟩,
⟨119,409097792,409098020⟩,
⟨128,439329460,439329704⟩]
theorem checked28951 : checkPrefixCuts (2^48) 3798597633 9 Manual.Count131072.C028951.packed 128 cuts28951 = true := by
 decide +kernel
def pointBounds28951 : List (Nat × Nat × Nat) := [(3798600704,104774688940874,104775072007899),(3798719488,104775088331611,104775471398858)]
theorem point_links_checked28951 : (cuts28951.take 2).map (fun c => (3798597633-1+2*2^9*c.k,104774679233819+c.lower,104775062300838+c.upper)) = pointBounds28951 := by
 decide +kernel
def cuts28952 : List PrefixCut := [⟨107,369517094,369517301⟩,
⟨128,440573986,440574232⟩]
theorem checked28952 : checkPrefixCuts (2^48) 3798728705 9 Manual.Count131072.C028952.packed 128 cuts28952 = true := by
 decide +kernel
def pointBounds28952 : List (Nat × Nat × Nat) := [(3798838272,104775488080373,104775871147843)]
theorem point_links_checked28952 : (cuts28952.take 1).map (fun c => (3798728705-1+2*2^9*c.k,104775118563279+c.lower,104775501630542+c.upper)) = pointBounds28952 := by
 decide +kernel
def cuts28953 : List PrefixCut := [⟨95,327271537,327271721⟩,
⟨128,440040092,440040341⟩]
theorem checked28953 : checkPrefixCuts (2^48) 3798859777 9 Manual.Count131072.C028953.packed 128 cuts28953 = true := by
 decide +kernel
def pointBounds28953 : List (Nat × Nat × Nat) := [(3798957056,104775886408802,104776269476495)]
theorem point_links_checked28953 : (cuts28953.take 1).map (fun c => (3798859777-1+2*2^9*c.k,104775559137265+c.lower,104775942204774+c.upper)) = pointBounds28953 := by
 decide +kernel
def cuts28954 : List PrefixCut := [⟨83,284806541,284806698⟩,
⟨128,441654889,441655134⟩]
theorem checked28954 : checkPrefixCuts (2^48) 3798990849 9 Manual.Count131072.C028954.packed 128 cuts28954 = true := by
 decide +kernel
def pointBounds28954 : List (Nat × Nat × Nat) := [(3799075840,104776283983898,104776667051813)]
theorem point_links_checked28954 : (cuts28954.take 1).map (fun c => (3798990849-1+2*2^9*c.k,104775999177357+c.lower,104776382245115+c.upper)) = pointBounds28954 := by
 decide +kernel
def cuts28955 : List PrefixCut := [⟨71,237602620,237602756⟩,
⟨128,434601219,434601467⟩]
theorem checked28955 : checkPrefixCuts (2^48) 3799121921 9 Manual.Count131072.C028955.packed 128 cuts28955 = true := by
 decide +kernel
def pointBounds28955 : List (Nat × Nat × Nat) := [(3799194624,104776678434866,104777061503005)]
theorem point_links_checked28955 : (cuts28955.take 1).map (fun c => (3799121921-1+2*2^9*c.k,104776440832246+c.lower,104776823900249+c.upper)) = pointBounds28955 := by
 decide +kernel
def cuts28956 : List PrefixCut := [⟨59,196106471,196106584⟩,
⟨128,428733486,428733730⟩]
theorem checked28956 : checkPrefixCuts (2^48) 3799252993 9 Manual.Count131072.C028956.packed 128 cuts28956 = true := by
 decide +kernel
def pointBounds28956 : List (Nat × Nat × Nat) := [(3799313408,104777071539936,104777454608300)]
theorem point_links_checked28956 : (cuts28956.take 1).map (fun c => (3799252993-1+2*2^9*c.k,104776875433465+c.lower,104777258501716+c.upper)) = pointBounds28956 := by
 decide +kernel
def cuts28957 : List PrefixCut := [⟨47,161725119,161725208⟩,
⟨128,436497501,436497744⟩]
theorem checked28957 : checkPrefixCuts (2^48) 3799384065 9 Manual.Count131072.C028957.packed 128 cuts28957 = true := by
 decide +kernel
def pointBounds28957 : List (Nat × Nat × Nat) := [(3799432192,104777465892070,104777848960654)]
theorem point_links_checked28957 : (cuts28957.take 1).map (fun c => (3799384065-1+2*2^9*c.k,104777304166951+c.lower,104777687235446+c.upper)) = pointBounds28957 := by
 decide +kernel
def cuts28958 : List PrefixCut := [⟨35,121567643,121567712⟩,
⟨128,441890283,441890528⟩]
theorem checked28958 : checkPrefixCuts (2^48) 3799515137 9 Manual.Count131072.C028958.packed 128 cuts28958 = true := by
 decide +kernel
def pointBounds28958 : List (Nat × Nat × Nat) := [(3799550976,104777862232095,104778245300902)]
theorem point_links_checked28958 : (cuts28958.take 1).map (fun c => (3799515137-1+2*2^9*c.k,104777740664452+c.lower,104778123733190+c.upper)) = pointBounds28958 := by
 decide +kernel
def cuts28959 : List PrefixCut := [⟨23,78449666,78449710⟩,
⟨128,439356325,439356574⟩]
theorem checked28959 : checkPrefixCuts (2^48) 3799646209 9 Manual.Count131072.C028959.packed 128 cuts28959 = true := by
 decide +kernel
def pointBounds28959 : List (Nat × Nat × Nat) := [(3799669760,104778261004401,104778644073428)]
theorem point_links_checked28959 : (cuts28959.take 1).map (fun c => (3799646209-1+2*2^9*c.k,104778182554735+c.lower,104778565623718+c.upper)) = pointBounds28959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000279
