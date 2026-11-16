import PlattPointSubsetKernel
import PlattPointPackets.S7B000277
import PlattPointPackets.S7B000278
import PlattPointPackets.S7B000279
import PlattPointPackets.S7B000280
import PlattPointPackets.S7B000281
import PlattPointPackets.S7B000282
import PlattPointPackets.S7B000283
import PlattPointPackets.S7B000284
import PlattPointPackets.S7B000285
import PlattPointPackets.S7B000286
import PlattPointPackets.S7B000287
import PlattPointPackets.S7B000288
import PlattPointPackets.S7B000289
import PlattPointPackets.S7B000290
import PlattPointPackets.S7B000291
import PlattPointPackets.S7B000292
import PlattPointPackets.S7B000293
import PlattPointPackets.S7B000294
import PlattPointPackets.S7B000295
import PlattGlobalGrid.S8B000104
namespace ChenEffective.PlattWindow.PointCovers.S8B000104
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000277.points ++ ChenEffective.PlattWindow.PointPackets.S7B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000285.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000286.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000288.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000290.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000291.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000295.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000104.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000104.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000104
