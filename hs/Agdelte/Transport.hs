{-# LANGUAGE OverloadedStrings #-}

-- | Transport abstraction: expose agents over HTTP and WebSocket.
--
-- Builds on Http.hs (raw sockets) and WebSocket.hs (WS framing)
-- to provide a high-level interface for serving agents.
--
-- This module bridges the gap between:
--   - Runtime.hs (generic agent runner with channels)
--   - AgentServer.hs (concrete multi-agent HTTP+WS server)
--
-- For ProcessOptic / RemoteOptic, this module will provide
-- the HTTP transport layer.

module Agdelte.Transport
  ( ServeConfig(..)
  , defaultConfig
  , serveAgent
  , serveAgentWithWs
  , RouteHandler
  , mkRouteHandler
  ) where

import qualified Data.Text as T
import Data.IORef

import qualified Agdelte.Http as Http
import qualified Agdelte.WebSocket as WS

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

data ServeConfig = ServeConfig
  { scPort :: Int
  , scCorsOrigin :: Maybe T.Text    -- ^ CORS Allow-Origin header (Nothing = no CORS)
  }

defaultConfig :: ServeConfig
defaultConfig = ServeConfig
  { scPort = 3000
  , scCorsOrigin = Just "*"
  }

------------------------------------------------------------------------
-- Route handler abstraction
------------------------------------------------------------------------

-- | A route handler maps (method, path, body) to a response
type RouteHandler = T.Text -> T.Text -> T.Text -> IO Http.Response

-- | Create a simple route handler for a single agent
-- GET  /state → observe
-- POST /step  → step with body
mkRouteHandler :: IO T.Text              -- ^ observe function
               -> (T.Text -> IO T.Text)  -- ^ step function
               -> RouteHandler
mkRouteHandler observe step method path body
  | path == "/state" && method == "GET" = do
      output <- observe
      return (Http.Response 200 output)
  | path == "/step" && method == "POST" = do
      output <- step body
      return (Http.Response 200 output)
  | otherwise =
      return (Http.Response 404 "Not found")

------------------------------------------------------------------------
-- Serve a single agent over HTTP
------------------------------------------------------------------------

-- | Serve a single agent on a port.
-- Routes:
--   GET  /state → current observation
--   POST /step  → step agent, return new observation
serveAgent :: ServeConfig
           -> IO T.Text              -- ^ observe
           -> (T.Text -> IO T.Text)  -- ^ step
           -> IO ()
serveAgent config observe step =
  Http.serve (scPort config) handler
  where
    handler :: Http.Request -> IO Http.Response
    handler req = do
      let rh = mkRouteHandler observe step
      resp <- rh (Http.reqMethod req) (Http.reqPath req) (Http.reqBody req)
      return $ addCors config resp

------------------------------------------------------------------------
-- Serve agent with WebSocket broadcast
------------------------------------------------------------------------

-- | Serve agent over HTTP + WebSocket.
-- HTTP for request/response, WS for broadcast on state changes.
-- The wsPath parameter specifies which path upgrades to WebSocket.
serveAgentWithWs :: ServeConfig
                 -> T.Text                             -- ^ WebSocket path (e.g. "/ws")
                 -> IO T.Text                          -- ^ observe
                 -> (T.Text -> IO T.Text)              -- ^ step
                 -> (WS.WsConn -> IO ())               -- ^ WS connection handler
                 -> IO ()
serveAgentWithWs config wsPath observe step wsHandler =
  Http.serveWithWs (scPort config) httpHandler (Just (wsPath, wsHandler))
  where
    httpHandler :: Http.Request -> IO Http.Response
    httpHandler req = do
      let rh = mkRouteHandler observe step
      resp <- rh (Http.reqMethod req) (Http.reqPath req) (Http.reqBody req)
      return $ addCors config resp

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

addCors :: ServeConfig -> Http.Response -> Http.Response
addCors config resp = case scCorsOrigin config of
  Nothing     -> resp
  Just origin -> resp { Http.resBody = Http.resBody resp }
  -- Note: CORS headers are added at the Http.hs level via formatResponse.
  -- This is a placeholder for when Http.hs supports custom headers.
