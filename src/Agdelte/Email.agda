{-# OPTIONS --without-K --guardedness #-}

-- Email sending via Haskell SMTP FFI.
-- Server-side only (GHC backend).

module Agdelte.Email where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Email types
------------------------------------------------------------------------

record SmtpConfig : Set where
  constructor mkSmtpConfig
  field
    smtpHost     : String
    smtpPort     : String         -- port as string (avoid ℕ FFI issues)
    smtpUser     : String
    smtpPassword : String
    smtpFrom     : String         -- sender email

open SmtpConfig public

record Email : Set where
  constructor mkEmail
  field
    emailTo      : String
    emailSubject : String
    emailBody    : String         -- plain text body

open Email public

------------------------------------------------------------------------
-- Send email (Haskell FFI)
------------------------------------------------------------------------

postulate
  sendEmailImpl : SmtpConfig → Email → IO ⊤

{-# FOREIGN GHC
  -- Placeholder: real implementation uses Network.Mail.SMTP or http-conduit
  -- for API-based services (SendGrid, Mailgun).
  --
  -- sendEmailImpl :: AgdaSmtpConfig -> AgdaEmail -> IO ()
  -- sendEmailImpl cfg email = do
  --   let from = Address Nothing (smtpFrom cfg)
  --       to   = [Address Nothing (emailTo email)]
  --       msg  = simpleMail from to [] [] (emailSubject email)
  --              [plainPart (emailBody email)]
  --   sendMailWithLoginTLS (smtpHost cfg) (smtpUser cfg) (smtpPassword cfg) msg

  import qualified Data.Text.IO as TIO

  sendEmailStub _ email = do
    TIO.putStrLn $ "EMAIL STUB: would send to <" <> emailTo' email <> ">"
    where emailTo' = error "sendEmailImpl: not yet implemented — replace this stub"
  #-}

{-# COMPILE GHC sendEmailImpl = \_ _ -> putStrLn "sendEmailImpl: stub — email not sent" #-}

------------------------------------------------------------------------
-- Email templates (locale-aware)
------------------------------------------------------------------------

open import Agdelte.I18n using (Locale; Ru; En)

-- | Registration confirmation email.
registrationEmail : Locale → String → String → Email
registrationEmail Ru toAddr userName = mkEmail toAddr
  "Добро пожаловать!"
  ("Здравствуйте, " ++ userName ++ "!\n\nВаш аккаунт успешно создан.\n")
registrationEmail En toAddr userName = mkEmail toAddr
  "Welcome!"
  ("Hello, " ++ userName ++ "!\n\nYour account has been created.\n")

-- | Purchase confirmation email.
purchaseEmail : Locale → String → String → String → Email
purchaseEmail Ru toAddr userName courseTitle = mkEmail toAddr
  ("Покупка курса: " ++ courseTitle)
  ("Здравствуйте, " ++ userName ++ "!\n\n"
   ++ "Вы приобрели курс \"" ++ courseTitle ++ "\".\nПриятного обучения!\n")
purchaseEmail En toAddr userName courseTitle = mkEmail toAddr
  ("Course purchased: " ++ courseTitle)
  ("Hello, " ++ userName ++ "!\n\n"
   ++ "You have purchased the course \"" ++ courseTitle ++ "\".\nEnjoy learning!\n")

-- | New lesson notification email.
newLessonEmail : Locale → String → String → String → Email
newLessonEmail Ru toAddr courseTitle lessonTitle = mkEmail toAddr
  ("Новый урок в курсе: " ++ courseTitle)
  ("В курсе \"" ++ courseTitle ++ "\" появился новый урок:\n"
   ++ "\"" ++ lessonTitle ++ "\"\n")
newLessonEmail En toAddr courseTitle lessonTitle = mkEmail toAddr
  ("New lesson in: " ++ courseTitle)
  ("A new lesson has been added to \"" ++ courseTitle ++ "\":\n"
   ++ "\"" ++ lessonTitle ++ "\"\n")
