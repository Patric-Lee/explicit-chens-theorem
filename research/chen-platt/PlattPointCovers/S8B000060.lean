import PlattPointSubsetKernel
import PlattPointPackets.S5B000261
import PlattPointPackets.S5B000262
import PlattPointPackets.S5B000263
import PlattPointPackets.S5B000264
import PlattPointPackets.S5B000265
import PlattPointPackets.S5B000266
import PlattPointPackets.S5B000267
import PlattPointPackets.S5B000268
import PlattPointPackets.S5B000269
import PlattPointPackets.S5B000270
import PlattPointPackets.S5B000271
import PlattPointPackets.S5B000272
import PlattPointPackets.S5B000273
import PlattGlobalGrid.S8B000060
namespace ChenEffective.PlattWindow.PointCovers.S8B000060
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000261.points ++ ChenEffective.PlattWindow.PointPackets.S5B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000273.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000060.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000060.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000060
