import PlattPointSubsetKernel
import PlattPointPackets.S7B000260
import PlattPointPackets.S7B000261
import PlattPointPackets.S7B000262
import PlattPointPackets.S7B000263
import PlattPointPackets.S7B000264
import PlattPointPackets.S7B000265
import PlattPointPackets.S7B000266
import PlattPointPackets.S7B000267
import PlattPointPackets.S7B000268
import PlattPointPackets.S7B000269
import PlattPointPackets.S7B000270
import PlattPointPackets.S7B000271
import PlattPointPackets.S7B000272
import PlattPointPackets.S7B000273
import PlattPointPackets.S7B000274
import PlattPointPackets.S7B000275
import PlattPointPackets.S7B000276
import PlattPointPackets.S7B000277
import PlattGlobalGrid.S8B000103
namespace ChenEffective.PlattWindow.PointCovers.S8B000103
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000260.points ++ ChenEffective.PlattWindow.PointPackets.S7B000261.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000277.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000103.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000103.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000103
